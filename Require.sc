RequiredFile {
    var <>path, <>result, <>cacheOn, <>sourceHash;
    
    *new { 
        |path, result| 
        ^super.newCopyArgs(path, result, [\evaluate]) 
    }
    
    == {
        |other|
        ^((path == other.path) && (sourceHash == other.sourceHash))
    }
    
    != {
        |other|
        ^(this == other).not
    }
}

Require {
    classvar <requireTable;
    classvar <roots;
    classvar <rootRequireCall=false;
    classvar cacheKeys;
    classvar setCacheAttribute;
    classvar requireDepth=0;
    classvar <>postRequires=true;
    
    *test {
        UnitTestScript("Require",
            Require.filenameSymbol.asString.dirname +/+ "Test" +/+ "Require_unittest.scd").runScript();
    }
    
    *initClass {
        roots = List();
        requireTable = IdentityDictionary();
        CmdPeriod.add(this);
        ServerTree.add(this);
        ServerBoot.add(this);
    }
    
    *prClearCache {
        |cacheKey|
        requireTable = requireTable.reject {
            |item|
            item.cacheOn.includes(cacheKey)
        }
    }
    
    *doOnCmdPeriod { this.prClearCache(\cmdPeriod) }
    *doOnServerBoot { this.prClearCache(\serverBoot) }
    *doOnServerTree { this.prClearCache(\serverTree) }
    *doOnEvaluate { this.prClearCache(\evaluate) }
    
    *reset {
        requireTable.clear();
    }
    
    *new {
        |identifier|
        ^this.require(identifier);
    }
    
    *with {
        |...identifiersAndFunc|
        var func = identifiersAndFunc.removeAt(identifiersAndFunc.size - 1);
        
        ^this.prEvaluateScope({
            func.value(
                *identifiersAndFunc.collect(this.require(_))
            )
        })
    }
    
    *prEvaluateScope {
        |func|
        var resetRootRequireCall = rootRequireCall;
        
        if (rootRequireCall.not) {
            rootRequireCall = true;
            this.doOnEvaluate();
            ^func.protect({
                rootRequireCall = resetRootRequireCall;
            });
        } {
            ^func.value();
        }   
    }
    
    *withRoot {
        |tempRoots, func|
        var oldRoots = roots;
        roots = tempRoots.isKindOf(String).if({ [tempRoots] }, tempRoots);
        protect(func, {
            roots = oldRoots;
        });
    }
    
    // A resolveRelative that always assumes the interpreter as parent.
    *resolveRelative {
        arg str, relativeTo;
        
        if (str[0] == thisProcess.platform.pathSeparator) { ^str };
        if (relativeTo.isNil) { ^str }; // It's okay if relativeTo is nil, just always resolve absolutely.
        ^(relativeTo.asString +/+ str)
    }
    
    *pathMatch {
        |str, extensions=(["scd"])|
        var result = (str ++ ".*").pathMatch ++ str.pathMatch;
        result = extensions.collectAs({
            |extension|
            result.select({
                |path|
                path.toLower.endsWith(extension.toLower);
            })
        }, result.class);
        ^result.flatten(1);
    }
    
    *canonicalPath {
        |path|
        ^File.realpath(PathName(path).asAbsolutePath().standardizePath).asSymbol();
    }
    
    *currentPath {
        var currentPath = thisProcess.nowExecutingPath;
        if (currentPath.isNil) { ^nil };
        currentPath = currentPath !? _.asString;
        if (PathName(currentPath).isFile) {
            currentPath = currentPath.dirname;
        };
        ^currentPath;
    }
    
    *currentPathAndRoots {
        var paths = roots.copy;
        this.currentPath !? { |current| paths = paths.insert(0, current) };
        ^paths;
    }
    
    *resolvePaths {
        |identifier, relativeTo, extensions=(["scd"]), attempts|
        var relativeBase, paths;
        
        relativeTo = relativeTo ?? { relativeTo = roots.copy };
        
        if (relativeTo.isKindOf(Collection).not || relativeTo.isKindOf(String)) {
            relativeTo = [relativeTo];
        };
        
        // Don't allow wildcard to be executed in a root directory.        
        if (identifier.contains("~")) {
            identifier = identifier.standardizePath;
        };
        
        // First match as if an absolute path
        paths = [];
        if (PathName(identifier).isAbsolutePath) {
            attempts.add(identifier);
            paths = this.pathMatch(identifier, extensions);
        };
        
        // Then relative
        relativeTo = relativeTo.detect {
            |relativeRoot|
            var resolved;
            
            if (paths.isEmpty()) {
                resolved = this.resolveRelative(identifier, relativeRoot);
                attempts.add(resolved);
                paths = this.pathMatch(resolved, extensions);
            };
            
            // Then relative with implicit ./
            if (paths.isEmpty() && (identifier[0] != ".")) {
                var tempIdentifier = "." +/+ identifier;
                resolved = this.resolveRelative(tempIdentifier, relativeRoot);
                attempts.add(resolved);
                paths = this.pathMatch(resolved, extensions);
                
                if (paths.notEmpty()) {
                    identifier = tempIdentifier
                }
            };
            
            paths.notEmpty();
        };
        
        extensions.do {
            |extension|
            var itentifierWithExt;
            // Then relative with implicit extension
            if (paths.isEmpty() && identifier.toLower.endsWith(extension.toLower).not) {
                itentifierWithExt = identifier ++ "." ++ extension;
                paths = this.pathMatch(this.resolveRelative(itentifierWithExt, relativeTo), [extension]);
            };
        };
        
        paths = paths.asSet.asArray.sort();
        ^paths;
    }
    
    *prGetSource {
        |path|
        ^File.readAllString(path)
    }
    
    *prGetSourceHash {
        |path|
        ^this.prGetSource(path).hash
    }
    
    *prIndentString {
        |depth|
        if (depth == 0) {
            ^""
        } {
            ^(
                ("  " ! depth).join ++ "└─ "
            )
        }
    }
    
    *prDoRequire {
        |path|
        var requiredFile, oldPath, func, cacheAttributeWasSet=false, time;
        
        requiredFile = RequiredFile();
        requiredFile.path = this.canonicalPath(path);
        requiredFile.sourceHash = this.prGetSourceHash(path.asString);
        
        requireTable[requiredFile.path] !? {
            |cached|
            if (
                cached.cacheOn.includes(\never) or: {
                    (cached.cacheOn.includes(\content)) 
                    and: { cached.sourceHash != requiredFile.sourceHash }
                }
            ) {
                requireTable[requiredFile.path] = nil;
            }
        };
        
        requireTable[requiredFile.path] !? {
            |cached|
            if (postRequires) {
                "%Require('%') [cached]".format(
                    this.prIndentString(requireDepth), 
                    path
                ).postln;
            };
            ^cached.result
        };
        
        if (postRequires) {
            "%Require('%')".format(
                this.prIndentString(requireDepth),
                path
            ).postln;        
        };
        
        requireDepth = requireDepth + 1;
        
        requireTable[requiredFile.path] = requiredFile;
        
        setCacheAttribute = {
            |...attributes|
            if (cacheAttributeWasSet) { 
                "Setting cache attribute twice in one file - the old setting will be lost".warn 
            };
            cacheAttributeWasSet = true;
            requiredFile.cacheOn = IdentitySet.newFrom(attributes);
        };
        
        func = thisProcess.interpreter.compileFile(requiredFile.path.asString);
        if (func.isNil) { Exception().throw() }; // failed to compile
        
        func = func.withPath(requiredFile.path.asString);
        
        time = Process.elapsedTime;
        requiredFile.result = protect(func, {
            setCacheAttribute = nil;
        });
        
        requireDepth = requireDepth - 1;
        
        ^requiredFile.result
    }
    
    *require {
        |identifier|
        var paths, results, attempts;
        
        identifier = identifier.asString();
        
        attempts = List();
        paths = this.resolvePaths(identifier, this.currentPathAndRoots, extensions:["scd"], attempts:attempts);
        
        if (paths.isEmpty) {
            "No files found, attempted paths: ".warn;
            attempts.do {
                |a|
                "\t%".format(*a).warn
            };
            Exception("No files found for Require(%)! (executing from: %)".format(identifier, thisProcess.nowExecutingPath)).throw;
        };
        
        this.prEvaluateScope {
            results = paths.collect(this.prDoRequire(_, requireDepth - 1));
        };
        
        if (results.size == 1) {
            ^results[0];
        } {
            ^results;
        }
    }
    
    *cache {
        |...attributes|
        var allowed = [\content, \serverBoot, \serverTree, \cmdPeriod, \never, \evaluate];
        var rejected = attributes.copy.difference(allowed);
        if (rejected.size > 0) {
            Error("Unknown attributes: % (possible values are: %)".format(rejected, allowed)).throw;
        };
        setCacheAttribute.value(*attributes);
    }
}

+Function {
    withPath {
        |path|        
        ^{
            var oldPath = thisProcess.nowExecutingPath;
            thisProcess.nowExecutingPath = path;
            protect(this, {
                thisProcess.nowExecutingPath = oldPath
            })
        }
    }
}


