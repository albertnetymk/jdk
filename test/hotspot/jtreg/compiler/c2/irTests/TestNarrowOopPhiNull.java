/*
 * Copyright (c) 2026, Alibaba Group Holding Limited. All Rights Reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */

package compiler.c2.irTests;

import compiler.lib.ir_framework.*;
import jdk.test.lib.Asserts;

/*
 * @test
 * @summary Keep Phi inputs narrow when merging a decoded oop with null
 * @requires vm.compiler2.enabled & vm.bits == "64"
 * @library /test/lib /
 * @run driver compiler.c2.irTests.TestNarrowOopPhiNull
 */
public class TestNarrowOopPhiNull {
    static class Holder {
        Object value;
    }

    private static Object result;

    public static void main(String[] args) {
        TestFramework framework = new TestFramework();
        framework.addFlags("-Xmx128m");
        // Test both conditional moves and retained Phis (ConditionalMoveLimit=0).
        framework.addScenarios(new Scenario(0),
                               new Scenario(1, "-XX:ConditionalMoveLimit=0"),
                               new Scenario(2, "-XX:-UseCompressedOops"));
        framework.start();
    }

    @Test
    @IR(failOn = {IRNode.ENCODE_P, IRNode.DECODE_N}, counts = {IRNode.STORE_N, "1"},
        applyIf = {"UseCompressedOops", "true"})
    public static void testTwoSelections(Holder src, int first, int second) {
        Object value = src.value;
        value = first == 0 ? null : value;
        result = second == 0 ? null : value;
    }

    @Run(test = "testTwoSelections")
    public static void check() {
        Holder src = new Holder();
        for (Object value : new Object[] {null, new Object()}) {
            src.value = value;
            for (int first = 0; first < 2; first++) {
                for (int second = 0; second < 2; second++) {
                    Object expected = first == 0 || second == 0 ? null : value;
                    testTwoSelections(src, first, second);
                    Asserts.assertSame(result, expected);
                }
            }
        }
    }
}
