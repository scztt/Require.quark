// UnitTestScript("Require", thisProcess.nowExecutingPath).runScript;
{
    |test|
    var r1Result, r2Result, assertIdentical, assertNotIdentical;
    //////////////////////////
    // Hack: UnitTestScript doens't properly set nowExecutingPath, so we have to do it manually.
    var oldPath = thisProcess.nowExecutingPath;
    thisProcess.nowExecutingPath = PathName(Require.filenameSymbol.asString).pathOnly +/+ "Test/Require_unittest.scd";
    //////////////////////////
    
    assertIdentical = {
        |a, b, msg=""|
        test.assert(a === b, "% (% === %)".format(msg, a.asString, b.asString));
    };
    
    assertNotIdentical = {
        |a, b, msg=""|
        test.assert(a !== b, "% (% !== %)".format(msg, a.asString, b.asString));
    };
    
    protect({
        Require.reset();
        
        ~required1_count = ~required2_count = 0;
        test.assertEquals(Require("Required1"), "Required1",
            "Require returns correct value");
        test.assertEquals(~required1_count, 1,
            "Relative require works");
        test.assertEquals(Require("Subdir/Required2"), "Required2",
            "Require subfolder returns correct value");
        test.assertEquals(~required2_count, 1,
            "Relative require in subfolder works");
        
        Require.reset();
        ~required1_count = ~required2_count = 0;
        Require("Required1");
        Require("Subdir/Required2");
        test.assert((~required1_count == 1) && (~required2_count == 1),
            "Requires were re-run after reset.");
        
        Require.reset();
        ~required1_count = ~required2_count = 0;
        assertIdentical.(
            Require("Required1"),
            Require("Required1"),
            "Duplicate invocations return identival values");
        test.assertEquals(~required1_count, 1,
            "Require was invoked multiple times");
        
        Require.reset();
        ~required1_count = ~required2_count = 0;
        assertNotIdentical.(
            Require("Required1", always:true),
            Require("Required1", always:true),
            "Duplicate invocations with always return non-identival values");
        test.assertEquals(~required1_count, 2,
            "Require was invoked multiple times");
        
        Require.reset();
        ~required1_count = ~required2_count = 0;
        ~required_duplicate = Require("Required1_duplicate");
        assertIdentical.(~required_duplicate[0], ~required_duplicate[1]);
        test.assertEquals(~required1_count, 1);
        
        // ~required1_count = ~required2_count = false;
        // "touch \"%\"".format(thisProcess.nowExecutingPath.dirname +/+ "Required1.scd").unixCmdGetStdOut;
        // "touch \"%\"".format(thisProcess.nowExecutingPath.dirname +/+ "Subdir/Required2.scd").unixCmdGetStdOut;
        // Require("Required1"); Require("Subdir/Required2");
        // test.assert(~required1_count && ~required2_count,
        //     "Require re-runs in case of file update.");
        
        // ~required1_count = ~required2_count = false;
        // Require("Required1"); Require("Subdir/Required2");
        // test.assert(~required1_count.not && ~required2_count.not,
        //     "New file mod time is properly cached.");
        
    }, { thisProcess.nowExecutingPath = oldPath })
}

