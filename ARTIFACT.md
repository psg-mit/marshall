# Sound and robust solid modeling via exact real arithmetic and continuity

##  ICFP 2019 Artifact Evaluation

## Getting Started

Thanks for evaluating this artifact!
This document describes the generic installation procedure for the MarshallB system as well as how to perform the example computations described in the paper.

### How to run the artifact

- You should first choose whether to run the artifact on a virtual machine (VM) we provide or just with the source code. Here are the links for downloads:
    * [TODO] VM
    * [TODO] Source code

- [TODO: version numbers for rlwrap, MPFR, and OPAM] The VM is already fully configured. If you choose the source, you should install rlwrap and MPFR, in addition to OPAM.

### What to evaluate

Our artifact consists of the following:

1. The MarshallB programming system, a programming language interpreter written in OCaml. Our artifact will permit running a REPL for the language.
2.  The StoneWorks library for MarshallB, which is several files of MarshallB code. Our artifact will permit processing these files, ensuring they typecheck, and allowing them to be used at the REPL.
3. Standalone MarshallB files and commands to execute the case studies from the paper, for which the paper describes computational results that we produced using MarshallB. These are as follows:
    - a. In Section 2, `collision_safe` returns `True`.
    - b. In Section 8.1, the image shown in Fig. 16 is produced as a bitmap image. We manually made monotone adjustments to the brightness of the image to make the depth more apparent afterwards.
    - c. In Section 8.2, the Hausdorff distance between the cone and its mesh approximation is computed to have a lower bound of 0.07 and an upper bound of 0.10.

Our artifact permits each of these computations to be run, producing expected results. In particular, each computation corresponds to running the commands for a certain file.
Running `marshall FILE` should produce as command-line output the output `FILE.expected_out`. For each example, we point out the key part of the expected output, as well as an estimate of running time.
- 3a. Running `marshall examples/icfp/cam_piston.asd` (0.3 seconds) produces as its last line `- : prop = True`, indicating that `collision_safe` returns `True`.
- 3b. [TODO] Running `marshall examples/icfp/plot2.asd` (XXX seconds) produces the an image `XXX.bmp` that should be the same as `XXX_expected.bmp` and monotone adjustments to the brightness of the image (to make the depth more apparent) would result in the image shown in Fig. 16 of the paper.
- 3c. Running `marshall examples/icfp/mesh_lt.asd` (31 minutes) produces as its last line
`- : prop = True`, indicating that `hausdorff3 cone cone_mesh < 0.1` returns `True`. Running `marshall examples/icfp/mesh_gt.asd` (35 minutes) produces as its last line
`- : prop = True`, indicating that `hausdorff3 cone cone_mesh > 0.07` returns `True`.

 We will provide timing estimates for each computation. Because producing the image takes on the order of hours to run, we may also provide code for generating a lower-resolution image.


## Step-By-Step instructions

### Loading libraries and running the REPL

[TODO]

### Quicker versions of 3b and 3c

[TODO]

3b: Change # of pixels.
3c: Relax the bounds for comparison.

### System requirements

[TODO: check minimum amount of RAM required.]