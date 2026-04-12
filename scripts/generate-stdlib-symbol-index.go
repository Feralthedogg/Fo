package main

import (
	"bytes"
	"fmt"
	"go/importer"
	"go/types"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"runtime"
	"sort"
	"strings"
)

type PackageData struct {
	Functions   []string
	Members     []string
	MemberTypes map[string]string
	FuncSigs    map[string]FuncSig
	StructFields map[string]map[string]string
	NamedUnderlying map[string]string
}

type FuncSig struct {
	Name             string
	FixedParamNames  []string
	FixedParamTypes  []string
	Variadic         bool
	VariadicName     string
	VariadicElemType string
	ResultTypes      []string
}

func main() {
	_, file, _, ok := runtime.Caller(0)
	if !ok {
		fatalf("cannot resolve script path")
	}
	root := filepath.Clean(filepath.Join(filepath.Dir(file), ".."))
	checkerPath := filepath.Join(root, "internal", "checker", "checker.fo")
	indexPath := filepath.Join(root, "internal", "checker", "stdlibindex_generated.go")

	packages := stdPackages()
	packageData := map[string]PackageData{}
	methodNames := map[string]map[string]struct{}{}
	methodSigs := map[string]map[string]FuncSig{}
	interfaceSigs := map[string][]FuncSig{}
	for _, pkgPath := range packages {
		pkg := mustImportStdPackage(pkgPath)
		pdata, recvNames, recvSigs, ifaceSigs := collectPackageData(pkg)
		packageData[pkgPath] = pdata
		for recv, names := range recvNames {
			if methodNames[recv] == nil {
				methodNames[recv] = map[string]struct{}{}
			}
			for name := range names {
				methodNames[recv][name] = struct{}{}
			}
		}
		for recv, sigs := range recvSigs {
			if methodSigs[recv] == nil {
				methodSigs[recv] = map[string]FuncSig{}
			}
			for name, sig := range sigs {
				methodSigs[recv][name] = sig
			}
		}
		for iface, sigs := range ifaceSigs {
			interfaceSigs[iface] = append(interfaceSigs[iface], sigs...)
		}
	}

	writeFile(indexPath, buildGoIndex(packageData, methodNames, methodSigs, interfaceSigs))
	replaceGeneratedSection(checkerPath, buildCheckerWrapperSection())
	fmt.Printf("Updated %s\n", indexPath)
	fmt.Printf("Updated %s\n", checkerPath)
}

func stdPackages() []string {
	out := mustCapture("go", "list", "std")
	lines := strings.Split(strings.TrimSpace(out), "\n")
	pkgs := make([]string, 0, len(lines))
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}
		if line == "builtin" {
			continue
		}
		if strings.HasPrefix(line, "cmd/") {
			continue
		}
		if strings.HasPrefix(line, "internal/") || strings.Contains(line, "/internal/") {
			continue
		}
		if strings.HasPrefix(line, "vendor/") || strings.Contains(line, "/vendor/") {
			continue
		}
		pkgs = append(pkgs, line)
	}
	sort.Strings(pkgs)
	return pkgs
}

func collectPackageData(pkg *types.Package) (PackageData, map[string]map[string]struct{}, map[string]map[string]FuncSig, map[string][]FuncSig) {
	scope := pkg.Scope()
	names := scope.Names()
	sort.Strings(names)

	funcNames := []string{}
	memberNames := []string{}
	memberTypes := map[string]string{}
	methodNames := map[string]map[string]struct{}{}
	funcSigs := map[string]FuncSig{}
	methodSigs := map[string]map[string]FuncSig{}
	interfaceSigs := map[string][]FuncSig{}
	namedUnderlying := map[string]string{}

	for _, name := range names {
		if !tokenIsExported(name) {
			continue
		}
		obj := scope.Lookup(name)
		switch item := obj.(type) {
		case *types.Func:
			sig := item.Type().(*types.Signature)
			if sig.Recv() == nil {
				funcNames = append(funcNames, name)
				funcSigs[name] = makeFuncSig(name, sig)
			}
		case *types.Const:
			memberNames = append(memberNames, name)
			memberTypes[name] = foTypeString(item.Type())
		case *types.Var:
			memberNames = append(memberNames, name)
			memberTypes[name] = foTypeString(item.Type())
		case *types.TypeName:
			memberNames = append(memberNames, name)
			namedType := foTypeString(item.Type())
			memberTypes[name] = namedType
			underlying := foUnderlyingTypeString(item.Type())
			if namedType != "" && namedType != "any" && underlying != "" && underlying != "any" && underlying != namedType {
				namedUnderlying[namedType] = underlying
			}
			collectMethods(item.Type(), methodNames, methodSigs)
			collectMethods(types.NewPointer(item.Type()), methodNames, methodSigs)
			if iface, ok := item.Type().Underlying().(*types.Interface); ok {
				interfaceSigs[namedType] = interfaceMethodSigs(iface)
			}
		}
	}

	sort.Strings(funcNames)
	sort.Strings(memberNames)
	return PackageData{
		Functions:   funcNames,
		Members:     memberNames,
		MemberTypes: memberTypes,
		FuncSigs:    funcSigs,
		StructFields: collectStructFields(pkg),
		NamedUnderlying: namedUnderlying,
	}, methodNames, methodSigs, interfaceSigs
}

func collectStructFields(pkg *types.Package) map[string]map[string]string {
	out := map[string]map[string]string{}
	scope := pkg.Scope()
	names := scope.Names()
	for _, name := range names {
		if !tokenIsExported(name) {
			continue
		}
		obj := scope.Lookup(name)
		typeName, ok := obj.(*types.TypeName)
		if !ok {
			continue
		}
		structType, ok := typeName.Type().Underlying().(*types.Struct)
		if !ok {
			continue
		}
		qname := foTypeString(typeName.Type())
		if qname == "" || qname == "any" {
			continue
		}
		fields := map[string]string{}
		for i := 0; i < structType.NumFields(); i++ {
			field := structType.Field(i)
			if !field.Exported() {
				continue
			}
			ftype := foTypeString(field.Type())
			if ftype == "" {
				ftype = "any"
			}
			fields[field.Name()] = ftype
		}
		out[qname] = fields
	}
	return out
}

func collectMethods(t types.Type, names map[string]map[string]struct{}, sigs map[string]map[string]FuncSig) {
	recv := foTypeString(t)
	if recv == "" || recv == "any" {
		return
	}
	set := types.NewMethodSet(t)
	for i := 0; i < set.Len(); i++ {
		sel := set.At(i)
		fn, ok := sel.Obj().(*types.Func)
		if !ok || !fn.Exported() {
			continue
		}
		if names[recv] == nil {
			names[recv] = map[string]struct{}{}
		}
		if sigs[recv] == nil {
			sigs[recv] = map[string]FuncSig{}
		}
		names[recv][fn.Name()] = struct{}{}
		sigs[recv][fn.Name()] = makeFuncSig(fn.Name(), fn.Type().(*types.Signature))
	}
}

func makeFuncSig(name string, sig *types.Signature) FuncSig {
	paramNames := []string{}
	paramTypes := []string{}
	paramCount := sig.Params().Len()
	lastIndex := paramCount - 1
	var variadicName string
	var variadicElemType string
	for i := 0; i < paramCount; i++ {
		param := sig.Params().At(i)
		pname := param.Name()
		if pname == "" {
			pname = fmt.Sprintf("arg%d", i+1)
		}
		ptype := param.Type()
		if sig.Variadic() && i == lastIndex {
			if slice, ok := ptype.(*types.Slice); ok {
				variadicName = pname
				variadicElemType = foTypeString(slice.Elem())
			} else {
				variadicName = pname
				variadicElemType = foTypeString(ptype)
			}
			continue
		}
		paramNames = append(paramNames, pname)
		paramTypes = append(paramTypes, foTypeString(ptype))
	}
	results := []string{}
	for i := 0; i < sig.Results().Len(); i++ {
		results = append(results, foTypeString(sig.Results().At(i).Type()))
	}
	return FuncSig{
		Name:             name,
		FixedParamNames:  paramNames,
		FixedParamTypes:  paramTypes,
		Variadic:         sig.Variadic(),
		VariadicName:     variadicName,
		VariadicElemType: variadicElemType,
		ResultTypes:      results,
	}
}

func interfaceMethodSigs(iface *types.Interface) []FuncSig {
	out := []FuncSig{}
	for i := 0; i < iface.NumMethods(); i++ {
		method := iface.Method(i)
		if !method.Exported() {
			continue
		}
		out = append(out, makeFuncSig(method.Name(), method.Type().(*types.Signature)))
	}
	sort.Slice(out, func(i, j int) bool { return out[i].Name < out[j].Name })
	return out
}

func foTypeString(t types.Type) string {
	switch tt := t.(type) {
	case *types.Basic:
		return basicTypeName(tt)
	case *types.TypeParam:
		if obj := tt.Obj(); obj != nil {
			return obj.Name()
		}
		return "any"
	case *types.Pointer:
		elem := foTypeString(tt.Elem())
		if elem == "" || elem == "any" {
			return "any"
		}
		return "*" + elem
	case *types.Slice:
		elem := foTypeString(tt.Elem())
		if elem == "" || elem == "any" {
			return "any"
		}
		return "[]" + elem
	case *types.Array:
		elem := foTypeString(tt.Elem())
		if elem == "" || elem == "any" {
			return "any"
		}
		return "[]" + elem
	case *types.Chan:
		elem := foTypeString(tt.Elem())
		if elem == "" || elem == "any" {
			return "any"
		}
		if tt.Dir() == types.RecvOnly {
			return "<-chan " + elem
		}
		return "chan " + elem
	case *types.Interface:
		if tt.NumMethods() == 0 {
			return "interface"
		}
		return "interface"
	case *types.Map:
		key := foTypeString(tt.Key())
		value := foTypeString(tt.Elem())
		if key == "" || value == "" || key == "any" || value == "any" {
			return "any"
		}
		return "map[" + key + "]" + value
	case *types.Tuple:
		items := []string{}
		for i := 0; i < tt.Len(); i++ {
			item := foTypeString(tt.At(i).Type())
			if item == "" || item == "any" {
				return "any"
			}
			items = append(items, item)
		}
		return "(" + strings.Join(items, ", ") + ")"
	case *types.Signature:
		return funcSignatureTypeName(tt)
	case *types.Named:
		return namedTypeName(tt)
	case *types.Alias:
		if obj := tt.Obj(); obj != nil && obj.Exported() {
			return qualifiedTypeName(obj)
		}
		return foTypeString(types.Unalias(tt))
	default:
		return "any"
	}
}

func namedTypeName(t *types.Named) string {
	base := qualifiedTypeName(t.Obj())
	if base == "" || base == "any" {
		return "any"
	}
	typeArgs := t.TypeArgs()
	if typeArgs == nil || typeArgs.Len() == 0 {
		return base
	}
	args := make([]string, 0, typeArgs.Len())
	for i := 0; i < typeArgs.Len(); i++ {
		arg := foTypeString(typeArgs.At(i))
		if arg == "" {
			arg = "any"
		}
		args = append(args, arg)
	}
	return base + "[" + strings.Join(args, ", ") + "]"
}

func foUnderlyingTypeString(t types.Type) string {
	switch tt := t.(type) {
	case *types.Named:
		return foUnderlyingTypeString(tt.Underlying())
	case *types.Alias:
		return foUnderlyingTypeString(types.Unalias(tt))
	case *types.Basic:
		return basicTypeName(tt)
	case *types.Pointer:
		elem := foUnderlyingTypeString(tt.Elem())
		if elem == "" || elem == "any" {
			return "any"
		}
		return "*" + elem
	case *types.Slice:
		elem := foUnderlyingTypeString(tt.Elem())
		if elem == "" || elem == "any" {
			return "any"
		}
		return "[]" + elem
	case *types.Array:
		elem := foUnderlyingTypeString(tt.Elem())
		if elem == "" || elem == "any" {
			return "any"
		}
		return "[]" + elem
	case *types.Map:
		key := foUnderlyingTypeString(tt.Key())
		value := foUnderlyingTypeString(tt.Elem())
		if key == "" || value == "" || key == "any" || value == "any" {
			return "any"
		}
		return "map[" + key + "]" + value
	case *types.Interface:
		return "interface"
	case *types.Chan:
		elem := foUnderlyingTypeString(tt.Elem())
		if elem == "" || elem == "any" {
			return "any"
		}
		if tt.Dir() == types.RecvOnly {
			return "<-chan " + elem
		}
		return "chan " + elem
	case *types.Tuple:
		items := []string{}
		for i := 0; i < tt.Len(); i++ {
			item := foUnderlyingTypeString(tt.At(i).Type())
			if item == "" || item == "any" {
				return "any"
			}
			items = append(items, item)
		}
		return "(" + strings.Join(items, ", ") + ")"
	case *types.Signature:
		return funcSignatureTypeName(tt)
	default:
		return "any"
	}
}

func funcSignatureTypeName(sig *types.Signature) string {
	params := []string{}
	for i := 0; i < sig.Params().Len(); i++ {
		paramType := sig.Params().At(i).Type()
		if sig.Variadic() && i+1 == sig.Params().Len() {
			if slice, ok := paramType.(*types.Slice); ok {
				params = append(params, "..."+foTypeString(slice.Elem()))
			} else {
				params = append(params, "..."+foTypeString(paramType))
			}
			continue
		}
		params = append(params, foTypeString(paramType))
	}
	results := []string{}
	for i := 0; i < sig.Results().Len(); i++ {
		results = append(results, foTypeString(sig.Results().At(i).Type()))
	}
	if len(params) == 0 && len(results) == 0 {
		return "func"
	}
	head := "func(" + strings.Join(params, ", ") + ")"
	if len(results) == 0 {
		return head
	}
	if len(results) == 1 {
		return head + " " + results[0]
	}
	return head + " (" + strings.Join(results, ", ") + ")"
}

func basicTypeName(t *types.Basic) string {
	if t.Kind() == types.Byte {
		return "byte"
	}
	if t.Kind() == types.Rune {
		return "rune"
	}
	switch t.Kind() {
	case types.Bool, types.UntypedBool:
		return "bool"
	case types.String, types.UntypedString:
		return "string"
	case types.Int, types.Int8, types.Int16, types.Int32, types.Int64, types.UntypedInt, types.UntypedRune:
		return "int"
	case types.Uint, types.Uint16, types.Uint32, types.Uint64, types.Uintptr:
		return "int"
	case types.Float32, types.Float64, types.UntypedFloat:
		return "float64"
	case types.UnsafePointer, types.UntypedNil, types.Complex64, types.Complex128, types.UntypedComplex:
		return "any"
	default:
		if t.Name() == "error" {
			return "error"
		}
		return t.Name()
	}
}

func qualifiedTypeName(obj types.Object) string {
	if obj == nil {
		return "any"
	}
	if pkg := obj.Pkg(); pkg != nil {
		return packageQualifier(pkg.Path()) + "." + obj.Name()
	}
	return obj.Name()
}

func packageQualifier(path string) string {
	if path == "" {
		return ""
	}
	parts := strings.Split(path, "/")
	return parts[len(parts)-1]
}

func buildGoIndex(packageData map[string]PackageData, methodNames map[string]map[string]struct{}, methodSigs map[string]map[string]FuncSig, interfaceSigs map[string][]FuncSig) string {
	var b strings.Builder
	b.WriteString("// Code generated by scripts/generate-stdlib-symbol-index.go. DO NOT EDIT.\n\n")
	b.WriteString("package checker\n\n")
	b.WriteString("import base \"github.com/Feralthedogg/Fo/stdlib/fo\"\n\n")
	writeGoStringSliceMap(&b, "packageFunctionNames", packageData, func(data PackageData) []string { return data.Functions })
	b.WriteString("\n")
	writeGoStringSliceMap(&b, "packageMemberNames", packageData, func(data PackageData) []string { return data.Members })
	b.WriteString("\n")
	writeGoMemberTypeMap(&b, packageData)
	b.WriteString("\n")
	writeGoMethodNameMap(&b, methodNames)
	b.WriteString("\n")
	writeGoPackageFuncSigMap(&b, packageData)
	b.WriteString("\n")
	writeGoMethodSigMap(&b, methodSigs)
	b.WriteString("\n")
	writeGoInterfaceSigMap(&b, interfaceSigs)
	b.WriteString("\n")
	writeGoStructFieldMap(&b, packageData)
	b.WriteString("\n")
	writeGoNamedUnderlyingMap(&b, packageData)
	b.WriteString("\n")
	b.WriteString("func PackageFunctionNames(path string) []string {\n")
	b.WriteString("    if names, ok := packageFunctionNames[path]; ok {\n")
	b.WriteString("        return names\n")
	b.WriteString("    }\n")
	b.WriteString("    return []string{}\n")
	b.WriteString("}\n\n")
	b.WriteString("func PackageMemberNames(path string) []string {\n")
	b.WriteString("    if names, ok := packageMemberNames[path]; ok {\n")
	b.WriteString("        return names\n")
	b.WriteString("    }\n")
	b.WriteString("    return []string{}\n")
	b.WriteString("}\n\n")
	b.WriteString("func PackageMemberType(path string, name string) string {\n")
	b.WriteString("    if names, ok := packageMemberTypes[path]; ok {\n")
	b.WriteString("        if typ, ok := names[name]; ok {\n")
	b.WriteString("            return typ\n")
	b.WriteString("        }\n")
	b.WriteString("    }\n")
	b.WriteString("    return \"\"\n")
	b.WriteString("}\n\n")
	b.WriteString("func MethodNames(receiverType string) []string {\n")
	b.WriteString("    if names, ok := methodNames[receiverType]; ok {\n")
	b.WriteString("        return names\n")
	b.WriteString("    }\n")
	b.WriteString("    return []string{}\n")
	b.WriteString("}\n")
	b.WriteString("\n")
	b.WriteString("func GeneratedStructFieldNames(typeName string) []string {\n")
	b.WriteString("    if fields, ok := structFieldNames[typeName]; ok {\n")
	b.WriteString("        return fields\n")
	b.WriteString("    }\n")
	b.WriteString("    return []string{}\n")
	b.WriteString("}\n\n")
	b.WriteString("func GeneratedStructFieldType(typeName string, fieldName string) string {\n")
	b.WriteString("    if fields, ok := structFieldTypes[typeName]; ok {\n")
	b.WriteString("        if typ, ok := fields[fieldName]; ok {\n")
	b.WriteString("            return typ\n")
	b.WriteString("        }\n")
	b.WriteString("    }\n")
	b.WriteString("    return \"\"\n")
	b.WriteString("}\n\n")
	b.WriteString("\n")
	b.WriteString("func PackageFuncPrototype(path string, name string) base.Option[FuncInfo] {\n")
	b.WriteString("    if sigs, ok := packageFunctionSigs[path]; ok {\n")
	b.WriteString("        if sig, ok := sigs[name]; ok {\n")
	b.WriteString("            return base.Some[FuncInfo]{Value0: sig.Prototype()}\n")
	b.WriteString("        }\n")
	b.WriteString("    }\n")
	b.WriteString("    return base.None[FuncInfo]{}\n")
	b.WriteString("}\n\n")
	b.WriteString("func PackageFuncSig(path string, name string, argCount int) base.Option[FuncInfo] {\n")
	b.WriteString("    if sigs, ok := packageFunctionSigs[path]; ok {\n")
	b.WriteString("        if sig, ok := sigs[name]; ok {\n")
	b.WriteString("            if value, ok := sig.Exact(argCount); ok {\n")
	b.WriteString("                return base.Some[FuncInfo]{Value0: value}\n")
	b.WriteString("            }\n")
	b.WriteString("            return base.None[FuncInfo]{}\n")
	b.WriteString("        }\n")
	b.WriteString("    }\n")
	b.WriteString("    return base.None[FuncInfo]{}\n")
	b.WriteString("}\n\n")
	b.WriteString("func MethodPrototype(receiverType string, name string) base.Option[FuncInfo] {\n")
	b.WriteString("    if sigs, ok := methodSigs[receiverType]; ok {\n")
	b.WriteString("        if sig, ok := sigs[name]; ok {\n")
	b.WriteString("            return base.Some[FuncInfo]{Value0: sig.Prototype()}\n")
	b.WriteString("        }\n")
	b.WriteString("    }\n")
	b.WriteString("    return base.None[FuncInfo]{}\n")
	b.WriteString("}\n\n")
	b.WriteString("func MethodSig(receiverType string, name string, argCount int) base.Option[FuncInfo] {\n")
	b.WriteString("    if sigs, ok := methodSigs[receiverType]; ok {\n")
	b.WriteString("        if sig, ok := sigs[name]; ok {\n")
	b.WriteString("            if value, ok := sig.Exact(argCount); ok {\n")
	b.WriteString("                return base.Some[FuncInfo]{Value0: value}\n")
	b.WriteString("            }\n")
	b.WriteString("            return base.None[FuncInfo]{}\n")
	b.WriteString("        }\n")
	b.WriteString("    }\n")
	b.WriteString("    return base.None[FuncInfo]{}\n")
	b.WriteString("}\n\n")
	b.WriteString("func InterfaceMethods(interfaceType string) []FuncInfo {\n")
	b.WriteString("    if methods, ok := interfaceMethods[interfaceType]; ok {\n")
	b.WriteString("        return methods\n")
	b.WriteString("    }\n")
	b.WriteString("    return []FuncInfo{}\n")
	b.WriteString("}\n\n")
	b.WriteString("func NamedUnderlyingType(typeName string) string {\n")
	b.WriteString("    if underlying, ok := namedUnderlyingTypes[typeName]; ok {\n")
	b.WriteString("        return underlying\n")
	b.WriteString("    }\n")
	b.WriteString("    return \"\"\n")
	b.WriteString("}\n\n")
	b.WriteString("type generatedFuncSig struct {\n")
	b.WriteString("    Name             string\n")
	b.WriteString("    FixedParamNames  []string\n")
	b.WriteString("    FixedParamTypes  []string\n")
	b.WriteString("    Variadic         bool\n")
	b.WriteString("    VariadicName     string\n")
	b.WriteString("    VariadicElemType string\n")
	b.WriteString("    ResultTypes      []string\n")
	b.WriteString("}\n\n")
	b.WriteString("func (sig generatedFuncSig) Prototype() FuncInfo {\n")
	b.WriteString("    return FuncInfo{Name: sig.Name, TypeParams: []string{}, ParamNames: sig.FixedParamNames, ParamTypes: sig.FixedParamTypes, ResultTypes: sig.ResultTypes}\n")
	b.WriteString("}\n\n")
	b.WriteString("func (sig generatedFuncSig) Exact(argCount int) (FuncInfo, bool) {\n")
	b.WriteString("    if sig.Variadic {\n")
	b.WriteString("        if argCount < len(sig.FixedParamTypes) {\n")
	b.WriteString("            return FuncInfo{}, false\n")
	b.WriteString("        }\n")
	b.WriteString("        return VariadicFuncInfo(sig.Name, sig.FixedParamNames, sig.FixedParamTypes, sig.VariadicElemType, argCount, sig.ResultTypes), true\n")
	b.WriteString("    }\n")
	b.WriteString("    if argCount != len(sig.FixedParamTypes) {\n")
	b.WriteString("        return FuncInfo{}, false\n")
	b.WriteString("    }\n")
	b.WriteString("    return sig.Prototype(), true\n")
	b.WriteString("}\n")
	return b.String()
}

func writeGoStringSliceMap(b *strings.Builder, name string, packageData map[string]PackageData, get func(PackageData) []string) {
	fmt.Fprintf(b, "var %s = map[string][]string{\n", name)
	for _, pkg := range sortedPackageKeys(packageData) {
		fmt.Fprintf(b, "    %s: %s,\n", goQuote(pkg), goStringSlice(get(packageData[pkg])))
	}
	b.WriteString("}\n")
}

func writeGoMemberTypeMap(b *strings.Builder, packageData map[string]PackageData) {
	b.WriteString("var packageMemberTypes = map[string]map[string]string{\n")
	for _, pkg := range sortedPackageKeys(packageData) {
		fmt.Fprintf(b, "    %s: {\n", goQuote(pkg))
		names := append([]string{}, packageData[pkg].Members...)
		sort.Strings(names)
		for _, name := range names {
			fmt.Fprintf(b, "        %s: %s,\n", goQuote(name), goQuote(packageData[pkg].MemberTypes[name]))
		}
		b.WriteString("    },\n")
	}
	b.WriteString("}\n")
}

func writeGoMethodNameMap(b *strings.Builder, methodNames map[string]map[string]struct{}) {
	b.WriteString("var methodNames = map[string][]string{\n")
	receivers := make([]string, 0, len(methodNames))
	for recv := range methodNames {
		receivers = append(receivers, recv)
	}
	sort.Strings(receivers)
	for _, recv := range receivers {
		fmt.Fprintf(b, "    %s: %s,\n", goQuote(recv), goStringSlice(sortedSet(methodNames[recv])))
	}
	b.WriteString("}\n")
}

func writeGoPackageFuncSigMap(b *strings.Builder, packageData map[string]PackageData) {
	b.WriteString("var packageFunctionSigs = map[string]map[string]generatedFuncSig{\n")
	for _, pkg := range sortedPackageKeys(packageData) {
		fmt.Fprintf(b, "    %s: {\n", goQuote(pkg))
		names := append([]string{}, packageData[pkg].Functions...)
		sort.Strings(names)
		for _, name := range names {
			fmt.Fprintf(b, "        %s: %s,\n", goQuote(name), goFuncSigLiteral(packageData[pkg].FuncSigs[name]))
		}
		b.WriteString("    },\n")
	}
	b.WriteString("}\n")
}

func writeGoMethodSigMap(b *strings.Builder, methodSigs map[string]map[string]FuncSig) {
	b.WriteString("var methodSigs = map[string]map[string]generatedFuncSig{\n")
	receivers := make([]string, 0, len(methodSigs))
	for recv := range methodSigs {
		receivers = append(receivers, recv)
	}
	sort.Strings(receivers)
	for _, recv := range receivers {
		fmt.Fprintf(b, "    %s: {\n", goQuote(recv))
		names := make([]string, 0, len(methodSigs[recv]))
		for name := range methodSigs[recv] {
			names = append(names, name)
		}
		sort.Strings(names)
		for _, name := range names {
			fmt.Fprintf(b, "        %s: %s,\n", goQuote(name), goFuncSigLiteral(methodSigs[recv][name]))
		}
		b.WriteString("    },\n")
	}
	b.WriteString("}\n")
}

func writeGoInterfaceSigMap(b *strings.Builder, interfaceSigs map[string][]FuncSig) {
	b.WriteString("var interfaceMethods = map[string][]FuncInfo{\n")
	names := make([]string, 0, len(interfaceSigs))
	for name := range interfaceSigs {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		b.WriteString("    " + goQuote(name) + ": []FuncInfo{")
		methods := interfaceSigs[name]
		for i, sig := range methods {
			if i > 0 {
				b.WriteString(", ")
			}
			b.WriteString(goFuncInfoLiteral(sig))
		}
		b.WriteString("},\n")
	}
	b.WriteString("}\n")
}

func writeGoStructFieldMap(b *strings.Builder, packageData map[string]PackageData) {
	merged := mergedStructFields(packageData)
	b.WriteString("var structFieldNames = map[string][]string{\n")
	structNames := make([]string, 0, len(merged))
	for name := range merged {
		structNames = append(structNames, name)
	}
	sort.Strings(structNames)
	for _, name := range structNames {
		fields := merged[name]
		fieldNames := make([]string, 0, len(fields))
		for fieldName := range fields {
			fieldNames = append(fieldNames, fieldName)
		}
		sort.Strings(fieldNames)
		fmt.Fprintf(b, "    %s: %s,\n", goQuote(name), goStringSlice(fieldNames))
	}
	b.WriteString("}\n\n")
	b.WriteString("var structFieldTypes = map[string]map[string]string{\n")
	for _, name := range structNames {
		fields := merged[name]
		fmt.Fprintf(b, "    %s: {\n", goQuote(name))
		fieldNames := make([]string, 0, len(fields))
		for fieldName := range fields {
			fieldNames = append(fieldNames, fieldName)
		}
		sort.Strings(fieldNames)
		for _, fieldName := range fieldNames {
			fmt.Fprintf(b, "        %s: %s,\n", goQuote(fieldName), goQuote(fields[fieldName]))
		}
		b.WriteString("    },\n")
	}
	b.WriteString("}\n")
}

func writeGoNamedUnderlyingMap(b *strings.Builder, packageData map[string]PackageData) {
	b.WriteString("var namedUnderlyingTypes = map[string]string{\n")
	merged := map[string]string{}
	for _, pkg := range sortedPackageKeys(packageData) {
		for name, underlying := range packageData[pkg].NamedUnderlying {
			if _, exists := merged[name]; !exists {
				merged[name] = underlying
			}
		}
	}
	names := make([]string, 0, len(merged))
	for name := range merged {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		fmt.Fprintf(b, "    %s: %s,\n", goQuote(name), goQuote(merged[name]))
	}
	b.WriteString("}\n")
}

func mergedStructFields(packageData map[string]PackageData) map[string]map[string]string {
	out := map[string]map[string]string{}
	for _, pkg := range sortedPackageKeys(packageData) {
		for typeName, fields := range packageData[pkg].StructFields {
			if out[typeName] == nil {
				out[typeName] = map[string]string{}
			}
			for fieldName, fieldType := range fields {
				if _, exists := out[typeName][fieldName]; !exists {
					out[typeName][fieldName] = fieldType
				}
			}
		}
	}
	return out
}

func lookupStructFields(packageData map[string]PackageData, typeName string) map[string]string {
	for _, pkg := range sortedPackageKeys(packageData) {
		if fields, ok := packageData[pkg].StructFields[typeName]; ok {
			return fields
		}
	}
	return map[string]string{}
}

func goFuncSigLiteral(sig FuncSig) string {
	return "generatedFuncSig{" +
		"Name: " + goQuote(sig.Name) + ", " +
		"FixedParamNames: " + goStringSlice(sig.FixedParamNames) + ", " +
		"FixedParamTypes: " + goStringSlice(sig.FixedParamTypes) + ", " +
		"Variadic: " + goBool(sig.Variadic) + ", " +
		"VariadicName: " + goQuote(sig.VariadicName) + ", " +
		"VariadicElemType: " + goQuote(sig.VariadicElemType) + ", " +
		"ResultTypes: " + goStringSlice(sig.ResultTypes) +
		"}"
}

func goFuncInfoLiteral(sig FuncSig) string {
	return "FuncInfo{" +
		"Name: " + goQuote(sig.Name) + ", " +
		"TypeParams: []string{}, " +
		"ParamNames: " + goStringSlice(sig.FixedParamNames) + ", " +
		"ParamTypes: " + goStringSlice(sig.FixedParamTypes) + ", " +
		"ResultTypes: " + goStringSlice(sig.ResultTypes) +
		"}"
}

func buildCheckerWrapperSection() string {
	return strings.Join([]string{
		"func StdlibGeneratedSentinelBegin() string {",
		"    return \"BEGIN\"",
		"}",
		"",
		"func StdlibPackageFunctionNames(path string) []string {",
		"    live := LivePackageFunctionNames(path)",
		"    if len(live) > 0 {",
		"        return live",
		"    }",
		"    return PackageFunctionNames(path)",
		"}",
		"",
		"func StdlibGeneratedPackageFuncPrototype(path string, name string) Option[FuncInfo] {",
		"    live := LivePackageFuncPrototype(path, name)",
		"    if !isNone[FuncInfo](live) {",
		"        return live",
		"    }",
		"    return PackageFuncPrototype(path, name)",
		"}",
		"",
		"func StdlibGeneratedPackageFuncSig(path string, name string, argCount int) Option[FuncInfo] {",
		"    live := LivePackageFuncSig(path, name, argCount)",
		"    if !isNone[FuncInfo](live) {",
		"        return live",
		"    }",
		"    return PackageFuncSig(path, name, argCount)",
		"}",
		"",
		"func StdlibPackageMemberNames(path string) []string {",
		"    live := LivePackageMemberNames(path)",
		"    if len(live) > 0 {",
		"        return live",
		"    }",
		"    return PackageMemberNames(path)",
		"}",
		"",
		"func StdlibGeneratedMemberType(path string, name string) string {",
		"    live := LivePackageMemberType(path, name)",
		"    if !(live == \"\") {",
		"        return live",
		"    }",
		"    return PackageMemberType(path, name)",
		"}",
		"",
		"func StdlibGeneratedMethodNames(receiverType string) []string {",
		"    live := LiveAnyMethodNames(receiverType)",
		"    if len(live) > 0 {",
		"        return live",
		"    }",
		"    return MethodNames(receiverType)",
		"}",
		"",
		"func StdlibStructFieldNames(typeName string) []string {",
		"    live := LiveAnyStructFieldNames(typeName)",
		"    if len(live) > 0 {",
		"        return live",
		"    }",
		"    return GeneratedStructFieldNames(typeName)",
		"}",
		"",
		"func StdlibStructFieldType(typeName string, fieldName string) string {",
		"    live := LiveAnyStructFieldType(typeName, fieldName)",
		"    if !(live == \"\") {",
		"        return live",
		"    }",
		"    return GeneratedStructFieldType(typeName, fieldName)",
		"}",
		"",
		"func StdlibInterfaceMethods(interfaceType string) []FuncInfo {",
		"    live := LiveAnyInterfaceMethods(interfaceType)",
		"    if len(live) > 0 {",
		"        return live",
		"    }",
		"    return InterfaceMethods(interfaceType)",
		"}",
		"",
		"func StdlibNamedUnderlyingType(typeName string) string {",
		"    live := LiveAnyNamedUnderlyingType(typeName)",
		"    if !(live == \"\") {",
		"        return live",
		"    }",
		"    return NamedUnderlyingType(typeName)",
		"}",
		"",
		"func StdlibGeneratedMethodPrototype(receiverType string, name string) Option[FuncInfo] {",
		"    live := LiveAnyMethodPrototype(receiverType, name)",
		"    if !isNone[FuncInfo](live) {",
		"        return live",
		"    }",
		"    return MethodPrototype(receiverType, name)",
		"}",
		"",
		"func StdlibGeneratedMethodSig(receiverType string, name string, argCount int) Option[FuncInfo] {",
		"    live := LiveAnyMethodSig(receiverType, name, argCount)",
		"    if !isNone[FuncInfo](live) {",
		"        return live",
		"    }",
		"    return MethodSig(receiverType, name, argCount)",
		"}",
		"",
		"func StdlibGeneratedSentinelEnd() string {",
		"    return \"END\"",
		"}",
		"",
	}, "\n")
}

func replaceGeneratedSection(checkerPath, section string) {
	input, err := os.ReadFile(checkerPath)
	if err != nil {
		fatalf("read %s: %v", checkerPath, err)
	}
	re := regexp.MustCompile(`(?s)func StdlibGeneratedSentinelBegin\(\) string \{\n    return "BEGIN"\n\}\n.*?func StdlibGeneratedSentinelEnd\(\) string \{\n    return "END"\n\}\n`)
	if !re.Match(input) {
		fatalf("failed to locate generated stdlib section in %s", checkerPath)
	}
	output := re.ReplaceAll(input, []byte(section))
	writeFile(checkerPath, string(output))
}

func writeFile(path, content string) {
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		fatalf("mkdir %s: %v", filepath.Dir(path), err)
	}
	if err := os.WriteFile(path, []byte(content), 0o644); err != nil {
		fatalf("write %s: %v", path, err)
	}
}

func mustImportStdPackage(path string) *types.Package {
	pkg, err := importer.Default().Import(path)
	if err != nil {
		fatalf("import %s: %v", path, err)
	}
	return pkg
}

func mustCapture(name string, args ...string) string {
	cmd := exec.Command(name, args...)
	var stdout bytes.Buffer
	var stderr bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr
	if err := cmd.Run(); err != nil {
		fatalf("%s %s failed: %v\n%s", name, strings.Join(args, " "), err, stderr.String())
	}
	return stdout.String()
}

func goQuote(value string) string {
	return fmt.Sprintf("%q", value)
}

func goStringSlice(items []string) string {
	if len(items) == 0 {
		return "[]string{}"
	}
	parts := make([]string, 0, len(items))
	for _, item := range items {
		parts = append(parts, goQuote(item))
	}
	return "[]string{" + strings.Join(parts, ", ") + "}"
}

func goBool(value bool) string {
	if value {
		return "true"
	}
	return "false"
}

func sortedPackageKeys(data map[string]PackageData) []string {
	keys := make([]string, 0, len(data))
	for key := range data {
		keys = append(keys, key)
	}
	sort.Strings(keys)
	return keys
}

func sortedSet(values map[string]struct{}) []string {
	items := make([]string, 0, len(values))
	for value := range values {
		items = append(items, value)
	}
	sort.Strings(items)
	return items
}

func tokenIsExported(name string) bool {
	if name == "" {
		return false
	}
	ch := name[0]
	return ch >= 'A' && ch <= 'Z'
}

func fatalf(format string, args ...any) {
	fmt.Fprintf(os.Stderr, format+"\n", args...)
	os.Exit(1)
}
