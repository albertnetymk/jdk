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

/*
 * @test
 * @summary Elide the redundant acquire/release fences around acquire-only and
 *          release-only weak CAS, since the matched rule's aq/rl annotation
 *          already supplies the ordering, while keeping an unrelated standalone
 *          release (e.g. a constructor final-field barrier) that merely precedes
 *          a plain reference weak CAS.  Also check that the weak CAS
 *          acquire/release/relaxed and seqcst rules select the matching
 *          instruction variant.
 * @library /test/lib /
 *
 * @requires vm.flagless
 * @requires os.arch=="riscv64" & vm.debug == true & vm.compiler2.enabled
 *
 * @build compiler.c2.riscv64.TestCASFenceElision
 *
 * @run driver compiler.c2.riscv64.TestCASFenceElision
 */

package compiler.c2.riscv64;

import java.lang.invoke.MethodHandles;
import java.lang.invoke.VarHandle;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;

import jdk.test.lib.process.OutputAnalyzer;
import jdk.test.lib.process.ProcessTools;

// Spawns a JVM with PrintOptoAssembly and checks, from the generated code, that
// the fence a release-only or acquire-only weak CAS would otherwise need is
// elided (the CAS annotation supplies the ordering), while a constructor/
// final-field release barrier that precedes a plain reference weak CAS is kept.
public class TestCASFenceElision {
    public static void main(String[] args) throws Throwable {
        String subject = "compiler.c2.riscv64.CASFenceElisionCases";
        String[] procArgs = {
            "-XX:+UnlockExperimentalVMOptions",
            "-XX:+UnlockDiagnosticVMOptions",
            "-XX:-UseZtso",
            // Use a barrier-free collector so reference CAS selects the generic
            // rules too; G1/Z/Shenandoah wrap reference CAS with their own
            // barrier rules that carry different mnemonics.
            "-XX:+UseParallelGC",
            "-XX:-BackgroundCompilation",
            "-XX:-TieredCompilation",
            "-XX:+PrintOptoAssembly",
            "-XX:CompileCommand=compileonly," + subject + "::test*",
            "-XX:+UseCompressedOops",
            // Force constructors to use a standalone MemBarRelease for
            // final-field publication rather than a MemBarStoreStore.
            "-XX:-UseStoreStoreForCtor",
            subject
        };

        ProcessBuilder pb = ProcessTools.createLimitedTestJavaProcessBuilder(procArgs);
        OutputAnalyzer output = new OutputAnalyzer(pb.start());
        output.stderrShouldBeEmptyIgnoreVMWarnings();
        output.stdoutShouldNotBeEmpty();
        output.shouldHaveExitValue(0);

        List<String> lines = output.asLines();

        // The expectation for each method lives next to it, as a Check on the
        // subject class; see CASFenceElisionCases.
        for (Check c : CASFenceElisionCases.CHECKS) {
            checkCompile(lines, c.method(), c.expected(), c.forbidden(), output);
        }
    }

    // The opto-assembly print block of a compiled method: from its
    // "- name: 'm'" metadata line up to the next method's metadata line (or
    // EOF).  Isolating the block keeps an expected instruction from matching
    // into a following method and lets the forbidden scan cover the whole
    // method rather than stopping at the last expected match.
    private static List<String> methodBlock(List<String> lines, String methodname, OutputAnalyzer output) {
        String needle = "'" + methodname + "'";
        int start = -1;
        for (int i = 0; i < lines.size(); i++) {
            if (lines.get(i).contains("- name:") && lines.get(i).contains(needle)) {
                start = i;
                break;
            }
        }
        if (start < 0) {
            throw new RuntimeException("Missing compiler output for " + methodname + "!\n\n" + output.getOutput());
        }
        int end = lines.size();
        for (int i = start + 1; i < lines.size(); i++) {
            if (lines.get(i).contains("- name:")) {
                end = i;
                break;
            }
        }
        return lines.subList(start, end);
    }

    // Within the method's block, check that each expected instruction occurs in
    // the order supplied, and that none of the forbidden ones occurs anywhere.
    private static void checkCompile(List<String> lines, String methodname,
                                     String[] expected, String[] forbidden, OutputAnalyzer output) {
        System.out.println("checkCompile(" + methodname + ")");

        List<String> block = methodBlock(lines, methodname, output);

        int idx = 0;
        for (String s : expected) {
            while (idx < block.size() && !block.get(idx).matches(".*" + s + ".*")) {
                idx++;
            }
            if (idx == block.size()) {
                throw new RuntimeException("Missing expected output " + s + " for " + methodname + "!\n\n" + output.getOutput());
            }
            idx++;
        }

        for (String s : forbidden) {
            for (String line : block) {
                if (line.matches(".*" + s + ".*")) {
                    throw new RuntimeException("Unexpected output " + s + " for " + methodname + ": " + line + "!\n\n" + output.getOutput());
                }
            }
        }
    }
}

// A compiled test method paired with the opto-assembly substrings that must
// (and must not) appear in its block, plus, in a comment, the reason.  Keeping
// it next to the method makes it easy to see what is expected and why.
record Check(String method, String[] expected, String[] forbidden) {}

// The compiled methods under inspection.  Package-private: the JVM launcher
// accepts a non-public main class with a public static main.
class CASFenceElisionCases {
    static final Object A = new Object();
    static final Object B = new Object();

    static final byte[] bytes = new byte[4];
    static final short[] shorts = new short[4];
    static final VarHandle BYTE_VH = MethodHandles.arrayElementVarHandle(byte[].class);
    static final VarHandle SHORT_VH = MethodHandles.arrayElementVarHandle(short[].class);

    final AtomicReference<Object> f_ref = new AtomicReference<>(A);
    final AtomicInteger f_int = new AtomicInteger(0);

    static final class Holder {
        final int x;
        final Object y;
        Holder(int x) { this.x = x; this.y = A; }
    }

    // A release weak CAS supplies its own release ordering through the rl
    // annotation on its store, so its leading fence (marked by C2AccessFence as
    // belonging to the access) is elided.  The marker must appear before the
    // CAS, and there is no other membar around a release-only CAS.  The
    // instruction must be the release (rl) variant.
    static final Check WEAK_CAS_RELEASE = new Check("testWeakCasRelease",
        new String[] { "#@unnecessary_membar_release_rvwmo",
                       "weak_cmpxchg_rel " },
        new String[] { "weak_cmpxchg_relaxed ",
                       "weak_cmpxchg_acq ",
                       "weak_cmpxchg_seqcst ",
                       "#@membar_acquire_rvwmo",
                       "#@membar_release_rvwmo" });

    public boolean testWeakCasRelease()
    {
        return f_ref.weakCompareAndSetRelease(A, B);
    }

    // An acquire weak CAS supplies its own acquire ordering through the aq
    // annotation on its load, so its trailing fence is elided.  The marker must
    // appear after the CAS, and there is no other membar around an acquire-only
    // CAS.  The instruction must be the acquire (aq) variant, not the seqcst
    // (aqrl) one: pinning the mnemonic makes this check the rule selection, not
    // just the fence elision.
    static final Check WEAK_CAS_ACQUIRE = new Check("testWeakCasAcquire",
        new String[] { "weak_cmpxchg_acq ",
                       "#@unnecessary_membar_acquire_rvwmo" },
        new String[] { "weak_cmpxchg_relaxed ",
                       "weak_cmpxchg_rel ",
                       "weak_cmpxchg_seqcst ",
                       "#@membar_acquire_rvwmo",
                       "#@membar_release_rvwmo" });

    public boolean testWeakCasAcquire()
    {
        return f_ref.weakCompareAndSetAcquire(A, B);
    }

    // The converse rule selection: a seqcst (volatile) weak CAS emits the seqcst
    // (aqrl) variant, and its paired leading/trailing fences are elided as well.
    static final Check WEAK_CAS_SEQCST = new Check("testWeakCasSeqcst",
        new String[] { "#@unnecessary_membar_release_rvwmo",
                       "weak_cmpxchg_seqcst ",
                       "#@unnecessary_membar_acquire_rvwmo" },
        new String[] { "weak_cmpxchg_relaxed ",
                       "weak_cmpxchg_acq ",
                       "weak_cmpxchg_rel ",
                       "#@membar_acquire_rvwmo",
                       "#@membar_release_rvwmo" });

    public boolean testWeakCasSeqcst()
    {
        return f_ref.weakCompareAndSetVolatile(A, B);
    }

    // A plain reference weak CAS is upgraded to release by
    // release_if_reference(), so it must select the release variant.  Unlike
    // WEAK_CAS_CTOR_PLAIN_REFERENCE it has no fence of its own, so no membar
    // marker may appear.  The pinned mnemonic is weak_cmpxchg_rel, not
    // weak_cmpxchg_relaxed: there is no relaxed reference variant (contrast
    // WEAK_CAS_PLAIN_INT).
    static final Check WEAK_CAS_PLAIN_REFERENCE = new Check("testWeakCasPlainReference",
        new String[] { "weak_cmpxchg_rel " },
        new String[] { "weak_cmpxchg_relaxed ",
                       "weak_cmpxchg_acq ",
                       "weak_cmpxchg_seqcst ",
                       "#@membar_acquire_rvwmo",
                       "#@membar_release_rvwmo" });

    public boolean testWeakCasPlainReference()
    {
        return f_ref.weakCompareAndSetPlain(A, B);
    }

    // Each of compareAndExchange's three orderings must select the matching
    // variant and elide the access's own fences.
    static final Check CAE_ACQUIRE = new Check("testCompareAndExchangeAcquire",
        new String[] { "cmpxchg_acq ",
                       "#@unnecessary_membar_acquire_rvwmo" },
        new String[] { "cmpxchg_rel ",
                       "cmpxchg_seqcst ",
                       "#@membar_acquire_rvwmo",
                       "#@membar_release_rvwmo" });

    public Object testCompareAndExchangeAcquire()
    {
        return f_ref.compareAndExchangeAcquire(A, B);
    }

    static final Check CAE_RELEASE = new Check("testCompareAndExchangeRelease",
        new String[] { "#@unnecessary_membar_release_rvwmo",
                       "cmpxchg_rel " },
        new String[] { "cmpxchg_acq ",
                       "cmpxchg_seqcst ",
                       "#@membar_acquire_rvwmo",
                       "#@membar_release_rvwmo" });

    public Object testCompareAndExchangeRelease()
    {
        return f_ref.compareAndExchangeRelease(A, B);
    }

    static final Check CAE_SEQCST = new Check("testCompareAndExchange",
        new String[] { "#@unnecessary_membar_release_rvwmo",
                       "cmpxchg_seqcst ",
                       "#@unnecessary_membar_acquire_rvwmo" },
        new String[] { "cmpxchg_acq ",
                       "cmpxchg_rel ",
                       "#@membar_acquire_rvwmo",
                       "#@membar_release_rvwmo" });

    public Object testCompareAndExchange()
    {
        return f_ref.compareAndExchange(A, B);
    }

    // A plain int weak CAS is not upgraded: release_if_reference() applies only
    // to reference types, so this one stays unordered and emits a fully relaxed
    // AMO with no fences at all -- the counterpart to
    // WEAK_CAS_PLAIN_REFERENCE, which selects the release variant.
    static final Check WEAK_CAS_PLAIN_INT = new Check("testWeakCasPlainInt",
        new String[] { "weak_cmpxchg_relaxed " },
        new String[] { "weak_cmpxchg_acq ",
                       "weak_cmpxchg_rel ",
                       "weak_cmpxchg_seqcst ",
                       "#@membar_acquire_rvwmo",
                       "#@membar_release_rvwmo" });

    public boolean testWeakCasPlainInt(int i)
    {
        return f_int.weakCompareAndSetPlain(i, i + 1);
    }

    // Byte/short acquire weak CAS take the same treatment: the Zacas helper's
    // word-load pre-check is itself acquiring (lw.aq, or lw + fence r,rw
    // without Zalasr), and the amocas carries aq, so the trailing fence is
    // redundant on every exit path too.
    static final Check WEAK_CAS_BYTE_ACQUIRE = new Check("testWeakCasByteAcquire",
        new String[] { "weak_cmpxchg_acq ",
                       "#@unnecessary_membar_acquire_rvwmo" },
        new String[] { "weak_cmpxchg_relaxed ",
                       "weak_cmpxchg_rel ",
                       "weak_cmpxchg_seqcst ",
                       "#@membar_acquire_rvwmo",
                       "#@membar_release_rvwmo" });

    public boolean testWeakCasByteAcquire()
    {
        return BYTE_VH.weakCompareAndSetAcquire(bytes, 0, (byte)0, (byte)1);
    }

    // As testWeakCasByteAcquire, for a short.
    static final Check WEAK_CAS_SHORT_ACQUIRE = new Check("testWeakCasShortAcquire",
        new String[] { "weak_cmpxchg_acq ",
                       "#@unnecessary_membar_acquire_rvwmo" },
        new String[] { "weak_cmpxchg_relaxed ",
                       "weak_cmpxchg_rel ",
                       "weak_cmpxchg_seqcst ",
                       "#@membar_acquire_rvwmo",
                       "#@membar_release_rvwmo" });

    public boolean testWeakCasShortAcquire()
    {
        return SHORT_VH.weakCompareAndSetAcquire(shorts, 0, (short)0, (short)1);
    }

    // A plain reference weak CAS receives MemNode::release through
    // release_if_reference() but has no fence of its own.  The constructor
    // release barrier directly precedes the CAS here (no intervening volatile
    // read), so the exact problematic topology is exercised: it must be kept
    // rather than attributed to the CAS.  The CAS itself must be the release
    // (rl) variant; it never selects a relaxed variant, which does not exist
    // for reference types.
    static final Check WEAK_CAS_CTOR_PLAIN_REFERENCE = new Check("testWeakCasCtorPlainReference",
        new String[] { "#@membar_release_rvwmo",
                       "weak_cmpxchg_rel " },
        new String[] { "weak_cmpxchg_relaxed ",
                       "weak_cmpxchg_acq ",
                       "weak_cmpxchg_seqcst ",
                       "#@membar_acquire_rvwmo" });

    public boolean testWeakCasCtorPlainReference(int i)
    {
        // A freshly constructed object is published by a plain reference CAS.
        // The expected value is a constant, so the constructor release fence
        // directly precedes the CAS; it must be kept.
        Holder h = new Holder(i);
        return f_ref.weakCompareAndSetPlain(B, h);
    }

    static final Check[] CHECKS = {
        WEAK_CAS_RELEASE,
        WEAK_CAS_ACQUIRE,
        WEAK_CAS_SEQCST,
        WEAK_CAS_PLAIN_REFERENCE,
        CAE_ACQUIRE,
        CAE_RELEASE,
        CAE_SEQCST,
        WEAK_CAS_PLAIN_INT,
        WEAK_CAS_BYTE_ACQUIRE,
        WEAK_CAS_SHORT_ACQUIRE,
        WEAK_CAS_CTOR_PLAIN_REFERENCE
    };

    public static void main(String[] args)
    {
        final CASFenceElisionCases t = new CASFenceElisionCases();
        for (int i = 0; i < 100_000; i++) {
            t.f_ref.set(A);
            t.f_int.set(0);
            t.testWeakCasRelease();
            t.testWeakCasAcquire();
            t.testWeakCasSeqcst();
            t.testWeakCasPlainReference();
            t.testCompareAndExchangeAcquire();
            t.testCompareAndExchangeRelease();
            t.testCompareAndExchange();
            t.testWeakCasPlainInt(i);
            t.testWeakCasByteAcquire();
            t.testWeakCasShortAcquire();
            t.testWeakCasCtorPlainReference(i);
        }
    }
}