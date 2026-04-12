package checker

import (
	base "github.com/Feralthedogg/Fo/stdlib/fo"
	"golang.org/x/tools/go/packages"
	"os"
	"path/filepath"
	"strings"
	"sync"
)

var (
	liveAnyOnce   sync.Once
	liveAnyMu     sync.Mutex
	liveAnyLoaded map[string]bool
	liveTypeOwner map[string]string
)

func liveEnsureAnyInit() {
	liveAnyOnce.Do(func() {
		liveAnyLoaded = map[string]bool{}
		liveTypeOwner = map[string]string{}
	})
}

func liveEnsurePackage(path string) {
	if path == "" {
		return
	}
	liveEnsureAnyInit()
	liveEnsureStdlib()
	liveAnyMu.Lock()
	if liveAnyLoaded[path] {
		liveAnyMu.Unlock()
		return
	}
	liveAnyLoaded[path] = true
	liveAnyMu.Unlock()

	cfg := &packages.Config{
		Mode: packages.NeedName | packages.NeedTypes | packages.NeedImports | packages.NeedDeps,
	}
	if dir := livePackageDir(path); dir != "" {
		cfg.Dir = dir
	}
	pkgs, err := packages.Load(cfg, path)
	if err != nil {
		return
	}
	for _, pkg := range pkgs {
		if pkg == nil || pkg.Types == nil {
			continue
		}
		pdata, recvNames, recvSigs, ifaceMethods := liveCollectPackageData(pkg.Types)
		liveAnyMu.Lock()
		liveStdlibPackageData[pkg.PkgPath] = pdata
		for typeName := range pdata.StructFields {
			liveTypeOwner[typeName] = pkg.PkgPath
		}
		for typeName := range pdata.NamedUnderlying {
			liveTypeOwner[typeName] = pkg.PkgPath
		}
		for typeName := range ifaceMethods {
			liveTypeOwner[typeName] = pkg.PkgPath
		}
		for recv, names := range recvNames {
			liveTypeOwner[liveNormalizeOwnerType(recv)] = pkg.PkgPath
			liveStdlibMethodNames[recv] = names
		}
		for recv, sigs := range recvSigs {
			liveTypeOwner[liveNormalizeOwnerType(recv)] = pkg.PkgPath
			liveStdlibMethodSigs[recv] = sigs
		}
		for iface, methods := range ifaceMethods {
			liveStdlibInterfaces[iface] = methods
		}
		liveAnyMu.Unlock()
	}
}

func livePackageDir(path string) string {
	if strings.HasPrefix(path, "github.com/Feralthedogg/Fo/") || path == "github.com/Feralthedogg/Fo" {
		if env := os.Getenv("FO_LIVE_PKG_DIR"); env != "" {
			return env
		}
		if wd, err := os.Getwd(); err == nil {
			candidate := filepath.Join(wd, ".fo-build-live")
			if _, err := os.Stat(filepath.Join(candidate, "go.mod")); err == nil {
				return candidate
			}
		}
	}
	return ""
}

func LiveAnyPackageFunctionNames(path string) []string {
	liveEnsurePackage(path)
	return LivePackageFunctionNames(path)
}

func LiveAnyPackageMemberNames(path string) []string {
	liveEnsurePackage(path)
	return LivePackageMemberNames(path)
}

func LiveAnyPackageMemberType(path string, name string) string {
	liveEnsurePackage(path)
	return LivePackageMemberType(path, name)
}

func LiveAnyPackageFuncPrototype(path string, name string) base.Option[FuncInfo] {
	liveEnsurePackage(path)
	return LivePackageFuncPrototype(path, name)
}

func LiveAnyPackageFuncSig(path string, name string, argCount int) base.Option[FuncInfo] {
	liveEnsurePackage(path)
	return LivePackageFuncSig(path, name, argCount)
}

func LiveAnyPreload(path string) {
	liveEnsurePackage(path)
}

func LiveAnyMethodNames(receiverType string) []string {
	liveEnsureType(receiverType)
	canonical := liveCanonicalReceiverType(receiverType)
	return LiveMethodNames(canonical)
}

func LiveAnyMethodPrototype(receiverType string, name string) base.Option[FuncInfo] {
	liveEnsureType(receiverType)
	canonical := liveCanonicalReceiverType(receiverType)
	return LiveMethodPrototype(canonical, name)
}

func LiveAnyMethodSig(receiverType string, name string, argCount int) base.Option[FuncInfo] {
	liveEnsureType(receiverType)
	canonical := liveCanonicalReceiverType(receiverType)
	return LiveMethodSig(canonical, name, argCount)
}

func LiveAnyStructFieldNames(typeName string) []string {
	liveEnsureType(typeName)
	canonical := liveCanonicalKnownType(typeName)
	if canonical == "" {
		canonical = typeName
	}
	return LiveStructFieldNames(canonical)
}

func LiveAnyStructFieldType(typeName string, fieldName string) string {
	liveEnsureType(typeName)
	canonical := liveCanonicalKnownType(typeName)
	if canonical == "" {
		canonical = typeName
	}
	return LiveStructFieldType(canonical, fieldName)
}

func LiveAnyHasStructType(typeName string) bool {
	liveEnsureType(typeName)
	canonical := liveCanonicalKnownType(typeName)
	if canonical == "" {
		canonical = typeName
	}
	liveAnyMu.Lock()
	defer liveAnyMu.Unlock()
	for _, pkg := range liveStdlibPackageData {
		if _, ok := pkg.StructFields[canonical]; ok {
			return true
		}
	}
	return false
}

func LiveAnyInterfaceMethods(interfaceType string) []FuncInfo {
	liveEnsureType(interfaceType)
	canonical := liveCanonicalKnownType(interfaceType)
	if canonical == "" {
		canonical = interfaceType
	}
	return LiveInterfaceMethods(canonical)
}

func LiveAnyNamedUnderlyingType(typeName string) string {
	liveEnsureType(typeName)
	canonical := liveCanonicalKnownType(typeName)
	if canonical == "" {
		canonical = typeName
	}
	return LiveNamedUnderlyingType(canonical)
}

func LiveAnyCanonicalTypeName(typeName string) string {
	liveEnsureType(typeName)
	return liveCanonicalKnownType(typeName)
}

func liveEnsureType(typeName string) {
	liveEnsureAnyInit()
	liveEnsureStdlib()
	owner := liveTypeOwnerFor(typeName)
	if owner == "" {
		return
	}
	liveEnsurePackage(owner)
}

func liveTypeOwnerFor(typeName string) string {
	liveAnyMu.Lock()
	defer liveAnyMu.Unlock()
	key := liveNormalizeOwnerType(typeName)
	if owner, ok := liveTypeOwner[key]; ok {
		return owner
	}
	canonical := liveCanonicalKnownTypeLocked(typeName)
	if canonical == "" {
		return ""
	}
	return liveTypeOwner[canonical]
}

func liveNormalizeOwnerType(typeName string) string {
	if strings.HasPrefix(typeName, "*") {
		return liveNormalizeOwnerType(strings.TrimPrefix(typeName, "*"))
	}
	if idx := strings.Index(typeName, "["); idx >= 0 {
		return typeName[:idx]
	}
	return typeName
}

func liveCanonicalKnownType(typeName string) string {
	liveAnyMu.Lock()
	defer liveAnyMu.Unlock()
	return liveCanonicalKnownTypeLocked(typeName)
}

func liveCanonicalReceiverType(typeName string) string {
	if strings.HasPrefix(typeName, "*") {
		canonical := liveCanonicalKnownType(strings.TrimPrefix(typeName, "*"))
		if canonical == "" {
			return typeName
		}
		return "*" + canonical
	}
	canonical := liveCanonicalKnownType(typeName)
	if canonical == "" {
		return typeName
	}
	return canonical
}

func liveCanonicalKnownTypeLocked(typeName string) string {
	key := liveNormalizeOwnerType(typeName)
	if _, ok := liveTypeOwner[key]; ok {
		return key
	}
	if aliasCanonical := liveCanonicalQualifiedAliasLocked(key); aliasCanonical != "" {
		return aliasCanonical
	}
	dot := strings.LastIndex(key, ".")
	if dot < 0 {
		return ""
	}
	suffix := key[dot:]
	match := ""
	for candidate := range liveTypeOwner {
		if strings.HasSuffix(candidate, suffix) {
			if match != "" {
				return ""
			}
			match = candidate
		}
	}
	return match
}

func liveCanonicalQualifiedAliasLocked(typeName string) string {
	dot := strings.LastIndex(typeName, ".")
	if dot < 0 {
		return ""
	}
	short := typeName[dot:]
	match := ""
	for candidate, owner := range liveTypeOwner {
		if owner == "" {
			continue
		}
		cdot := strings.LastIndex(candidate, ".")
		if cdot < 0 {
			continue
		}
		if candidate[cdot:] != short {
			continue
		}
		if match != "" && match != candidate {
			return ""
		}
		match = candidate
	}
	return match
}
