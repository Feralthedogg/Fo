package checker

import (
	base "github.com/Feralthedogg/Fo/stdlib/fo"
	"go/importer"
	"go/types"
	"os/exec"
	"sort"
	"strings"
	"sync"
)

type livePackageData struct {
	Functions       []string
	Members         []string
	MemberTypes     map[string]string
	FuncSigs        map[string]liveFuncSig
	StructFields    map[string]map[string]string
	NamedUnderlying map[string]string
}

type liveFuncSig struct {
	Name             string
	FixedParamNames  []string
	FixedParamTypes  []string
	Variadic         bool
	VariadicName     string
	VariadicElemType string
	ResultTypes      []string
}

func (sig liveFuncSig) Prototype() FuncInfo {
	return FuncInfo{
		Name:        sig.Name,
		TypeParams:  []string{},
		ParamNames:  sig.FixedParamNames,
		ParamTypes:  sig.FixedParamTypes,
		ResultTypes: sig.ResultTypes,
	}
}

func (sig liveFuncSig) Exact(argCount int) (FuncInfo, bool) {
	if sig.Variadic {
		if argCount < len(sig.FixedParamTypes) {
			return FuncInfo{}, false
		}
		return VariadicFuncInfo(sig.Name, sig.FixedParamNames, sig.FixedParamTypes, sig.VariadicElemType, argCount, sig.ResultTypes), true
	}
	if argCount != len(sig.FixedParamTypes) {
		return FuncInfo{}, false
	}
	return sig.Prototype(), true
}

var (
	liveStdlibOnce          sync.Once
	liveStdlibPackageData   map[string]livePackageData
	liveStdlibMethodNames   map[string][]string
	liveStdlibMethodSigs    map[string]map[string]liveFuncSig
	liveStdlibInterfaces    map[string][]FuncInfo
	liveStdlibInitErr       error
)

func LivePackageFunctionNames(path string) []string {
	liveEnsureStdlib()
	if liveStdlibInitErr != nil {
		return []string{}
	}
	liveAnyMu.Lock()
	defer liveAnyMu.Unlock()
	if pkg, ok := liveStdlibPackageData[path]; ok {
		return pkg.Functions
	}
	return []string{}
}

func LivePackageMemberNames(path string) []string {
	liveEnsureStdlib()
	if liveStdlibInitErr != nil {
		return []string{}
	}
	liveAnyMu.Lock()
	defer liveAnyMu.Unlock()
	if pkg, ok := liveStdlibPackageData[path]; ok {
		return pkg.Members
	}
	return []string{}
}

func LivePackageMemberType(path string, name string) string {
	liveEnsureStdlib()
	if liveStdlibInitErr != nil {
		return ""
	}
	liveAnyMu.Lock()
	defer liveAnyMu.Unlock()
	if pkg, ok := liveStdlibPackageData[path]; ok {
		return pkg.MemberTypes[name]
	}
	return ""
}

func LivePackageFuncPrototype(path string, name string) base.Option[FuncInfo] {
	liveEnsureStdlib()
	if liveStdlibInitErr != nil {
		return base.None[FuncInfo]{}
	}
	liveAnyMu.Lock()
	defer liveAnyMu.Unlock()
	if pkg, ok := liveStdlibPackageData[path]; ok {
		if sig, ok := pkg.FuncSigs[name]; ok {
			return base.Some[FuncInfo]{Value0: sig.Prototype()}
		}
	}
	return base.None[FuncInfo]{}
}

func LivePackageFuncSig(path string, name string, argCount int) base.Option[FuncInfo] {
	liveEnsureStdlib()
	if liveStdlibInitErr != nil {
		return base.None[FuncInfo]{}
	}
	liveAnyMu.Lock()
	defer liveAnyMu.Unlock()
	if pkg, ok := liveStdlibPackageData[path]; ok {
		if sig, ok := pkg.FuncSigs[name]; ok {
			if value, ok := sig.Exact(argCount); ok {
				return base.Some[FuncInfo]{Value0: value}
			}
		}
	}
	return base.None[FuncInfo]{}
}

func LiveMethodNames(receiverType string) []string {
	liveEnsureStdlib()
	if liveStdlibInitErr != nil {
		return []string{}
	}
	liveAnyMu.Lock()
	defer liveAnyMu.Unlock()
	if names, ok := liveStdlibMethodNames[receiverType]; ok {
		return names
	}
	return []string{}
}

func LiveMethodPrototype(receiverType string, name string) base.Option[FuncInfo] {
	liveEnsureStdlib()
	if liveStdlibInitErr != nil {
		return base.None[FuncInfo]{}
	}
	liveAnyMu.Lock()
	defer liveAnyMu.Unlock()
	if sigs, ok := liveStdlibMethodSigs[receiverType]; ok {
		if sig, ok := sigs[name]; ok {
			return base.Some[FuncInfo]{Value0: sig.Prototype()}
		}
	}
	return base.None[FuncInfo]{}
}

func LiveMethodSig(receiverType string, name string, argCount int) base.Option[FuncInfo] {
	liveEnsureStdlib()
	if liveStdlibInitErr != nil {
		return base.None[FuncInfo]{}
	}
	liveAnyMu.Lock()
	defer liveAnyMu.Unlock()
	if sigs, ok := liveStdlibMethodSigs[receiverType]; ok {
		if sig, ok := sigs[name]; ok {
			if value, ok := sig.Exact(argCount); ok {
				return base.Some[FuncInfo]{Value0: value}
			}
		}
	}
	return base.None[FuncInfo]{}
}

func LiveStructFieldNames(typeName string) []string {
	liveEnsureStdlib()
	if liveStdlibInitErr != nil {
		return []string{}
	}
	liveAnyMu.Lock()
	defer liveAnyMu.Unlock()
	fields := map[string]string{}
	for _, pkg := range liveStdlibPackageData {
		if item, ok := pkg.StructFields[typeName]; ok {
			fields = item
			break
		}
	}
	if len(fields) == 0 {
		return []string{}
	}
	names := make([]string, 0, len(fields))
	for name := range fields {
		names = append(names, name)
	}
	sort.Strings(names)
	return names
}

func LiveStructFieldType(typeName string, fieldName string) string {
	liveEnsureStdlib()
	if liveStdlibInitErr != nil {
		return ""
	}
	liveAnyMu.Lock()
	defer liveAnyMu.Unlock()
	for _, pkg := range liveStdlibPackageData {
		if fields, ok := pkg.StructFields[typeName]; ok {
			return fields[fieldName]
		}
	}
	return ""
}

func LiveInterfaceMethods(interfaceType string) []FuncInfo {
	liveEnsureStdlib()
	if liveStdlibInitErr != nil {
		return []FuncInfo{}
	}
	liveAnyMu.Lock()
	defer liveAnyMu.Unlock()
	if methods, ok := liveStdlibInterfaces[interfaceType]; ok {
		return methods
	}
	return []FuncInfo{}
}

func LiveNamedUnderlyingType(typeName string) string {
	liveEnsureStdlib()
	if liveStdlibInitErr != nil {
		return ""
	}
	liveAnyMu.Lock()
	defer liveAnyMu.Unlock()
	for _, pkg := range liveStdlibPackageData {
		if underlying, ok := pkg.NamedUnderlying[typeName]; ok {
			return underlying
		}
	}
	return ""
}

func liveEnsureStdlib() {
	liveStdlibOnce.Do(func() {
		liveStdlibPackageData = map[string]livePackageData{}
		liveStdlibMethodNames = map[string][]string{}
		liveStdlibMethodSigs = map[string]map[string]liveFuncSig{}
		liveStdlibInterfaces = map[string][]FuncInfo{}

		pkgs, err := liveStdPackages()
		if err != nil {
			liveStdlibInitErr = err
			return
		}
		imp := importer.Default()
		for _, path := range pkgs {
			pkg, err := imp.Import(path)
			if err != nil {
				continue
			}
			pdata, recvNames, recvSigs, ifaceMethods := liveCollectPackageData(pkg)
			liveStdlibPackageData[path] = pdata
			for recv, names := range recvNames {
				liveStdlibMethodNames[recv] = names
			}
			for recv, sigs := range recvSigs {
				liveStdlibMethodSigs[recv] = sigs
			}
			for iface, methods := range ifaceMethods {
				liveStdlibInterfaces[iface] = methods
			}
		}
	})
}

func liveStdPackages() ([]string, error) {
	out, err := exec.Command("go", "list", "std").Output()
	if err != nil {
		return nil, err
	}
	lines := strings.Split(strings.TrimSpace(string(out)), "\n")
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
	return pkgs, nil
}

func liveCollectPackageData(pkg *types.Package) (livePackageData, map[string][]string, map[string]map[string]liveFuncSig, map[string][]FuncInfo) {
	scope := pkg.Scope()
	names := scope.Names()
	sort.Strings(names)

	funcNames := []string{}
	memberNames := []string{}
	memberTypes := map[string]string{}
	funcSigs := map[string]liveFuncSig{}
	structFields := liveCollectStructFields(pkg)
	namedUnderlying := map[string]string{}
	methodNames := map[string][]string{}
	methodSigs := map[string]map[string]liveFuncSig{}
	interfaceMethods := map[string][]FuncInfo{}

	for _, name := range names {
		obj := scope.Lookup(name)
		if obj == nil || !obj.Exported() {
			continue
		}
		switch item := obj.(type) {
		case *types.Func:
			sig := item.Type().(*types.Signature)
			if sig.Recv() == nil {
				funcNames = append(funcNames, name)
				funcSigs[name] = liveMakeFuncSig(name, sig)
			}
		case *types.Const:
			memberNames = append(memberNames, name)
			memberTypes[name] = liveTypeString(item.Type())
		case *types.Var:
			memberNames = append(memberNames, name)
			memberTypes[name] = liveTypeString(item.Type())
		case *types.TypeName:
			memberNames = append(memberNames, name)
			namedType := liveTypeString(item.Type())
			memberTypes[name] = namedType
			underlying := liveUnderlyingTypeString(item.Type())
			if liveShouldRecordUnderlying(namedType, underlying) {
				namedUnderlying[namedType] = underlying
			}
			liveCollectMethods(item.Type(), methodNames, methodSigs)
			liveCollectMethods(types.NewPointer(item.Type()), methodNames, methodSigs)
			if iface, ok := item.Type().Underlying().(*types.Interface); ok {
				interfaceMethods[namedType] = liveInterfaceMethods(iface)
			}
		}
	}

	sort.Strings(funcNames)
	sort.Strings(memberNames)
	return livePackageData{
		Functions:       funcNames,
		Members:         memberNames,
		MemberTypes:     memberTypes,
		FuncSigs:        funcSigs,
		StructFields:    structFields,
		NamedUnderlying: namedUnderlying,
	}, methodNames, methodSigs, interfaceMethods
}

func liveCollectStructFields(pkg *types.Package) map[string]map[string]string {
	out := map[string]map[string]string{}
	scope := pkg.Scope()
	for _, name := range scope.Names() {
		obj := scope.Lookup(name)
		typeName, ok := obj.(*types.TypeName)
		if !ok || typeName == nil || !typeName.Exported() {
			continue
		}
		structType, ok := typeName.Type().Underlying().(*types.Struct)
		if !ok {
			continue
		}
		qname := liveTypeString(typeName.Type())
		if qname == "" || qname == "any" {
			continue
		}
		fields := map[string]string{}
		for i := 0; i < structType.NumFields(); i++ {
			field := structType.Field(i)
			if !field.Exported() {
				continue
			}
			ftype := liveTypeString(field.Type())
			if ftype == "" {
				ftype = "any"
			}
			fields[field.Name()] = ftype
		}
		out[qname] = fields
	}
	return out
}

func liveCollectMethods(t types.Type, names map[string][]string, sigs map[string]map[string]liveFuncSig) {
	recv := liveTypeString(t)
	if recv == "" || recv == "any" {
		return
	}
	set := types.NewMethodSet(t)
	nameSet := map[string]struct{}{}
	if existing, ok := names[recv]; ok {
		for _, name := range existing {
			nameSet[name] = struct{}{}
		}
	}
	if sigs[recv] == nil {
		sigs[recv] = map[string]liveFuncSig{}
	}
	for i := 0; i < set.Len(); i++ {
		sel := set.At(i)
		fn, ok := sel.Obj().(*types.Func)
		if !ok || !fn.Exported() {
			continue
		}
		nameSet[fn.Name()] = struct{}{}
		sigs[recv][fn.Name()] = liveMakeFuncSig(fn.Name(), fn.Type().(*types.Signature))
	}
	list := make([]string, 0, len(nameSet))
	for name := range nameSet {
		list = append(list, name)
	}
	sort.Strings(list)
	names[recv] = list
}

func liveInterfaceMethods(iface *types.Interface) []FuncInfo {
	out := []FuncInfo{}
	for i := 0; i < iface.NumMethods(); i++ {
		method := iface.Method(i)
		if !method.Exported() {
			continue
		}
		out = append(out, liveMakeFuncSig(method.Name(), method.Type().(*types.Signature)).Prototype())
	}
	sort.Slice(out, func(i, j int) bool { return out[i].Name < out[j].Name })
	return out
}

func liveMakeFuncSig(name string, sig *types.Signature) liveFuncSig {
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
			pname = "arg"
		}
		ptype := param.Type()
		if sig.Variadic() && i == lastIndex {
			if slice, ok := ptype.(*types.Slice); ok {
				variadicName = pname
				variadicElemType = liveTypeString(slice.Elem())
			} else {
				variadicName = pname
				variadicElemType = liveTypeString(ptype)
			}
			continue
		}
		paramNames = append(paramNames, pname)
		paramTypes = append(paramTypes, liveTypeString(ptype))
	}
	results := []string{}
	for i := 0; i < sig.Results().Len(); i++ {
		results = append(results, liveTypeString(sig.Results().At(i).Type()))
	}
	return liveFuncSig{
		Name:             name,
		FixedParamNames:  paramNames,
		FixedParamTypes:  paramTypes,
		Variadic:         sig.Variadic(),
		VariadicName:     variadicName,
		VariadicElemType: variadicElemType,
		ResultTypes:      results,
	}
}

func liveTypeString(t types.Type) string {
	switch tt := t.(type) {
	case *types.Basic:
		return liveBasicTypeName(tt)
	case *types.TypeParam:
		if obj := tt.Obj(); obj != nil {
			return obj.Name()
		}
		return "any"
	case *types.Pointer:
		elem := liveTypeString(tt.Elem())
		if elem == "" || elem == "any" {
			return "any"
		}
		return "*" + elem
	case *types.Slice:
		elem := liveTypeString(tt.Elem())
		if elem == "" || elem == "any" {
			return "any"
		}
		return "[]" + elem
	case *types.Array:
		elem := liveTypeString(tt.Elem())
		if elem == "" || elem == "any" {
			return "any"
		}
		return "[]" + elem
	case *types.Chan:
		elem := liveTypeString(tt.Elem())
		if elem == "" || elem == "any" {
			return "any"
		}
		if tt.Dir() == types.RecvOnly {
			return "<-chan " + elem
		}
		return "chan " + elem
	case *types.Interface:
		return "interface"
	case *types.Map:
		key := liveTypeString(tt.Key())
		value := liveTypeString(tt.Elem())
		if key == "" || value == "" || key == "any" || value == "any" {
			return "any"
		}
		return "map[" + key + "]" + value
	case *types.Tuple:
		items := []string{}
		for i := 0; i < tt.Len(); i++ {
			item := liveTypeString(tt.At(i).Type())
			if item == "" || item == "any" {
				return "any"
			}
			items = append(items, item)
		}
		return "(" + strings.Join(items, ", ") + ")"
	case *types.Signature:
		return liveFuncSignatureTypeName(tt)
	case *types.Named:
		return liveNamedTypeName(tt)
	case *types.Alias:
		if obj := tt.Obj(); obj != nil && obj.Exported() {
			return liveQualifiedTypeName(obj)
		}
		return liveTypeString(types.Unalias(tt))
	default:
		return "any"
	}
}

func liveUnderlyingTypeString(t types.Type) string {
	switch tt := t.(type) {
	case *types.Named:
		return liveUnderlyingTypeString(tt.Underlying())
	case *types.Alias:
		return liveUnderlyingTypeString(types.Unalias(tt))
	case *types.Basic:
		return liveBasicTypeName(tt)
	case *types.Pointer:
		elem := liveUnderlyingTypeString(tt.Elem())
		if elem == "" || elem == "any" {
			return "any"
		}
		return "*" + elem
	case *types.Slice:
		elem := liveUnderlyingTypeString(tt.Elem())
		if elem == "" || elem == "any" {
			return "any"
		}
		return "[]" + elem
	case *types.Array:
		elem := liveUnderlyingTypeString(tt.Elem())
		if elem == "" || elem == "any" {
			return "any"
		}
		return "[]" + elem
	case *types.Map:
		key := liveUnderlyingTypeString(tt.Key())
		value := liveUnderlyingTypeString(tt.Elem())
		if key == "" || value == "" || key == "any" || value == "any" {
			return "any"
		}
		return "map[" + key + "]" + value
	case *types.Interface:
		return "interface"
	case *types.Chan:
		elem := liveUnderlyingTypeString(tt.Elem())
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
			item := liveUnderlyingTypeString(tt.At(i).Type())
			if item == "" || item == "any" {
				return "any"
			}
			items = append(items, item)
		}
		return "(" + strings.Join(items, ", ") + ")"
	case *types.Signature:
		return liveFuncSignatureTypeName(tt)
	case *types.Struct:
		return "struct"
	default:
		return "any"
	}
}

func liveShouldRecordUnderlying(namedType string, underlying string) bool {
	if namedType == "" || namedType == "any" {
		return false
	}
	if underlying == "" || underlying == "any" || underlying == namedType {
		return false
	}
	if strings.HasPrefix(underlying, "[]") {
		return true
	}
	if strings.HasPrefix(underlying, "map[") {
		return true
	}
	if strings.HasPrefix(underlying, "chan ") || strings.HasPrefix(underlying, "<-chan ") {
		return true
	}
	if strings.HasPrefix(underlying, "func") {
		return true
	}
	if strings.HasPrefix(underlying, "*") {
		return true
	}
	return false
}

func liveFuncSignatureTypeName(sig *types.Signature) string {
	params := []string{}
	for i := 0; i < sig.Params().Len(); i++ {
		paramType := sig.Params().At(i).Type()
		if sig.Variadic() && i+1 == sig.Params().Len() {
			if slice, ok := paramType.(*types.Slice); ok {
				params = append(params, "..."+liveTypeString(slice.Elem()))
			} else {
				params = append(params, "..."+liveTypeString(paramType))
			}
			continue
		}
		params = append(params, liveTypeString(paramType))
	}
	results := []string{}
	for i := 0; i < sig.Results().Len(); i++ {
		results = append(results, liveTypeString(sig.Results().At(i).Type()))
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

func liveBasicTypeName(t *types.Basic) string {
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
	case types.Int, types.Int8, types.Int16, types.UntypedInt:
		return "int"
	case types.Int32:
		return "int32"
	case types.Int64:
		return "int64"
	case types.UntypedRune:
		return "rune"
	case types.Uint, types.Uint16, types.Uintptr:
		return "uint"
	case types.Uint8:
		return "byte"
	case types.Uint32:
		return "uint32"
	case types.Uint64:
		return "uint64"
	case types.Float32:
		return "float32"
	case types.Float64, types.UntypedFloat:
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

func liveNamedTypeName(t *types.Named) string {
	base := liveQualifiedTypeName(t.Obj())
	if base == "" || base == "any" {
		return "any"
	}
	typeArgs := t.TypeArgs()
	if typeArgs == nil || typeArgs.Len() == 0 {
		return base
	}
	args := make([]string, 0, typeArgs.Len())
	for i := 0; i < typeArgs.Len(); i++ {
		arg := liveTypeString(typeArgs.At(i))
		if arg == "" {
			arg = "any"
		}
		args = append(args, arg)
	}
	return base + "[" + strings.Join(args, ", ") + "]"
}

func liveQualifiedTypeName(obj types.Object) string {
	if obj == nil {
		return "any"
	}
	if pkg := obj.Pkg(); pkg != nil {
		return livePackageQualifier(pkg.Path()) + "." + obj.Name()
	}
	return obj.Name()
}

func livePackageQualifier(path string) string {
	if path == "" {
		return ""
	}
	parts := strings.Split(path, "/")
	return parts[len(parts)-1]
}
