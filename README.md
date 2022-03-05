# LW-CSP-Prover and MBP-Prover

# Introduction
 "LW-CSP-Prover" and "MBP-Prover" are theory-files used in the generic theorem prover Isabelle2021, in order to formally verify the correctness of the parallelization algorithm in the Model-Based Parallelizer (MBP). LW-CSP-Prover is a light-weight version of [CSP-Prover](https://staff.aist.go.jp/y-isobe/CSP-Prover/CSP-Prover.html).

# Theory files
 - LW-CSP-Prover : a package of theory-files for the formal specification language (CSP)
   * CSP_trace.thy : Trace
   * CSP_syntax.thy : Syntax of CSP
   * CSP_semantics.thy : Semantics of CSP
   * CSP_wsim.thy : Trace refinement and weak simulation
   * CSP_wfsim.thy : Failures refinement and weak failures simulation


 - MBP-Prover : a package of theory-files for the Model-Based Parallelizer (MBP)
   * MBP_bace.thy : Basic definitions used in MBP
   * MBP_algo.thy : The algorithm for parallelizing control models
   * MBP_spec.thy : The definition of specifications
   * SeqCtrl_safe.thy : The safety property in specifications
   * SeqCtrl_all.thy : The liveness property in specifications
   * ParaCtrl_safe.thy : The safety property in parallel control models
   * ParaCtrl_all.thy : The liveness property in parallel control models

# Installation
 The MBP-Prover/LW-CSP-Prover needs the theorem prover [Isabelle2021](https://isabelle.in.tum.de/).

# Licence
 The MBP-Prover/LW-CSP-Prover is released under the [MIT license](https://en.wikipedia.org/wiki/MIT_License), see [LICENSE.txt](LICENSE.txt).
 
# References
1. Zhaoqian Zhong and Masato Edahiro, Model-Based Parallelizer for Multi- / Many-Core Processors, 2017-EMB-44, No47, pp.1-6, 2017.

1. Shunya Tamon, Yoshinao Isobe, Masato Edahiro, Formalization and Correctness-Proof of Model-Based Parallelization Algorithm, ETNET2019, Vol.2019-EMB-50, No.9, pp.1-8, 2019.

1. Shun Iwata, Yoshinao Isobe, and Masato Edahiro, Formal Verification of the Model Based parallelization Algorithm by a Theorem Prover, ETNET2022, EMB, March 2022 (to be published).
