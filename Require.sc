RequiredFile {
    var <>path, <>result, <>mtime;
    
    *new { |path, result, mtime| ^super.newCopyArgs(path, result, mtime) }
        
        == {
            |other|
            ^((path == other.path) && (mtime == other.mtime))
        }
        
        != {
            |other|
            ^(this == other).not
        }
}

Require {
    classvar <requireTable;
    classvar <roots;
    classvar rootRequireCall=false;
    
    *test {
        UnitTestScript("Require",
            Require.filenameSymbol.asString.dirname +/+ "Test" +/+ "Require_unittest.scd").runScript();
    }
    
    *initClass {
        roots = List();
        requireTable = IdentityDictionary();
        CmdPeriod.add({ this.reset() })
    }
    
    *reset {
        requireTable.clear();
    }
    
    *new {
        arg identifier, cmdPeriod = false, always = false;
        ^this.require(identifier, cmdPeriod, always);
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
        
        relativeTo ?? { relativeTo = roots.copy };
        
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
    
    *require {
        arg identifier, cmdPeriod = false, always = false;
        var paths, results, caller, attempts, isRoot = false;
        
        attempts = List();
        identifier = identifier.asString();
        this.currentPath();
        paths = this.resolvePaths(identifier, this.currentPathAndRoots, extensions:["scd"], attempts:attempts);
        
        if (paths.isEmpty) {
            "No files found, attempted paths: ".warn;
            attempts.do {
                |a|
                "\t%".format(*a).warn
            };
            Exception("No files found for Require(%)! (executing from: %)".format(identifier, thisProcess.nowExecutingPath)).throw;
        } {
            if (rootRequireCall.not) {
                rootRequireCall = true;
                thisThread.clock.sched(0, {
                    // wait for all Require calls to finish, then reset our cache
                    rootRequireCall = false;
                    requireTable.clear();
                })
            };
            
            results = paths.collect({
                |path|
                var requiredFile, oldPath, func;
                
                requiredFile = RequiredFile();
                requiredFile.path = this.canonicalPath(path);
                requiredFile.mtime = File.mtime(requiredFile.path);
                
                if (always or: {requireTable[requiredFile.path].isNil or:{ requireTable[requiredFile.path].mtime != requiredFile.mtime}}) {
                    oldPath = thisProcess.nowExecutingPath;
                    thisProcess.nowExecutingPath = requiredFile.path.asString;
                    
                    protect {
                        func = thisProcess.interpreter.compileFile(requiredFile.path.asString);
                        if (func.isNil) { Exception().throw() }; // failed to compile
                        requiredFile.result = func.value();
                        requireTable[requiredFile.path] = requiredFile;
                    } {
                        |e|
                        
                        if (e.notNil) {
                            "Require of file % failed!".format(requiredFile.path).error;
                            requireTable[requiredFile.path] = nil;
                        };
                        
                        thisProcess.nowExecutingPath = oldPath;
                    };
                    
                    if (cmdPeriod) {
                        CmdPeriod.doOnce({
                            requireTable[requiredFile.path] = nil;
                        })
                    }
                } {
                    requiredFile = requireTable[requiredFile.path];
                };
                
                requiredFile.result;
            });                
        };
        
        if (results.size == 1) {
            ^results[0];
        } {
            ^results;
        }
    }
}
