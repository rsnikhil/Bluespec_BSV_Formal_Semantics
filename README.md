# Bluespec_BSV_Formal_Semantics
Formal semantics of BSV (Bluespec SystemVerilog), given as a Haskell Program and accompanying document

BSV is a High-level Hardware Design Language (HLHDL), taking its inspirations from Haskell and Term Rewriting Systems.
A commercial implementation of BSV (a compiler from BSV into Verilog) has been available from
Bluespec, Inc. (www.bluespec.com) since 2004, and has been used for several industrial-strength hardware designs.
There is a growing interest in <i>formal verification of hardware designs</i>.
BSV is attractive because of its clean semantics and formal foundations.

This repository is an independent, <i>implementation-independent</i> formal specification of BSV semantics.
It is an <i>executable</i> semantics, given as a Haskell program, in the directory <tt>Haskell_code</tt>.
That directory also contains several example (kernel) BSV programs,
and transcripts of example runs through the semantic function.
It is a <i>dynamic</i> semantics, describing direct execution of the abstract syntax of a (parsed) program,
and thus takes no position on pre-computation of rule schedules; it just describes correct execution of
any given rule schedule.

All of this is explained in detail in the accompanying document: <tt>Paper/BSV_Semantics.pdf</tt>
