/*
 * Copyright (c) 2026, Alibaba Group Holding Limited. All rights reserved.
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

package compiler.c2;

import compiler.lib.ir_framework.*;
import jdk.test.lib.Asserts;

/**
 * @test
 * @summary Implicit null checks of a compressed oop whose memory access uses a
 *          separately decoded pointer.
 * @library /test/lib /
 * @requires vm.bits == "64" & vm.compiler2.enabled
 * @run driver compiler.c2.TestImplicitNullCheckDecode
 */
public class TestImplicitNullCheckDecode {

    static class Node {
        Node next;
        int f;
    }

    public static void main(String[] args) {
        TestFramework framework = new TestFramework();
        framework.addFlags("-XX:-TieredCompilation", "-Xbatch");
        framework.addScenarios(
                // Uncompressed oops: the full pointer is compared against null
                // and used as the address base.
                new Scenario(0, "-XX:-UseCompressedOops"),
                // Small heap with the default alignment, so unscaled or
                // zero-based compressed oops. Depending on the platform, the
                // decode folds into the address or the null check is done on
                // the decoded pointer.
                new Scenario(1, "-Xms64m", "-Xmx128m"),
                // A shift of 4 prevents the decode from folding into the
                // address on all platforms. HeapBaseMinAddress=64g asks for a
                // heap above the zero-based range (4G << 4 = 64G), so the
                // narrow oop is compared against null and the access uses a
                // separate DecodeN. If the heap still ends up zero-based, the
                // null check is done on the decoded pointer and the IR rules
                // hold as well.
                new Scenario(2, "-XX:ObjectAlignmentInBytes=16",
                             "-XX:HeapBaseMinAddress=64g"));
        framework.start();
    }

    @Test
    // On AIX, the zero page is readable, so loads through a null pointer do not
    // trap. See os::zero_page_read_protected(). The same holds for the tests
    // below.
    //
    // With a shift of 4, both the check of n and the check of n.next are
    // implicit. The latter uses the separately decoded n.next as address base.
    @IR(applyIfPlatform = {"aix", "false"},
        applyIfAnd = {"ObjectAlignmentInBytes", "16", "UseCompressedOops", "true"},
        counts = {IRNode.NULL_CHECK, "2"},
        phase = CompilePhase.FINAL_CODE)
    @IR(applyIfPlatform = {"aix", "false"},
        counts = {IRNode.NULL_CHECK, ">= 1"},
        phase = CompilePhase.FINAL_CODE)
    static int loadNext(Node n) {
        return n.next.f;
    }

    @Test
    @IR(applyIfPlatform = {"aix", "false"},
        applyIfAnd = {"ObjectAlignmentInBytes", "16", "UseCompressedOops", "true"},
        counts = {IRNode.NULL_CHECK, "2"},
        phase = CompilePhase.FINAL_CODE)
    @IR(applyIfPlatform = {"aix", "false"},
        counts = {IRNode.NULL_CHECK, ">= 1"},
        phase = CompilePhase.FINAL_CODE)
    static void storeNext(Node n, int v) {
        n.next.f = v;
    }

    @DontInline
    static void consume(Node n) {}

    @Test
    // The decoded n.next is also passed to the call, so the DecodeN has a user
    // besides the access that becomes the null check.
    @IR(applyIfPlatform = {"aix", "false"},
        applyIfAnd = {"ObjectAlignmentInBytes", "16", "UseCompressedOops", "true"},
        counts = {IRNode.NULL_CHECK, "2"},
        phase = CompilePhase.FINAL_CODE)
    @IR(applyIfPlatform = {"aix", "false"},
        counts = {IRNode.NULL_CHECK, ">= 1"},
        phase = CompilePhase.FINAL_CODE)
    static int loadThenCall(Node n) {
        Node m = n.next;
        int x = m.f;
        consume(m);
        return x;
    }

    @Run(test = {"loadNext", "storeNext", "loadThenCall"},
         mode = RunMode.STANDALONE)
    static void run() {
        Node n = new Node();
        n.next = new Node();
        // Trigger compilation with implicit null checks.
        for (int i = 0; i < 10_000; i++) {
            loadNext(n);
            storeNext(n, i);
            loadThenCall(n);
        }
        // Trigger null pointer exceptions in the compiled code.
        n.next = null;
        Asserts.assertThrows(NullPointerException.class, () -> loadNext(n));
        Asserts.assertThrows(NullPointerException.class, () -> storeNext(n, 1));
        Asserts.assertThrows(NullPointerException.class, () -> loadThenCall(n));
    }
}
