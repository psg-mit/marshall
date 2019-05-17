# Sound and robust solid modeling via exact real arithmetic and continuity

##  ICFP 2019 Artifact Evaluation

## Getting Started

Thanks for evaluating this artifact!
This document describes the generic installation procedure for the MarshallB system as well as how to perform the example computations described in the paper.

### How to run the artifact

You should first choose whether to run the artifact on a Docker image we provide or just with the source code.

#### Docker image:

First, download the Docker image:
[TODO] Docker  image.

To run the Docker image, run
```
docker load < marshallb.tar.gz    #load docker image
docker run -it marshallb          #run docker image
```

Once at the interactive terminal, the `marshall` program will be available as a command-line program.
The entire source directory is located at `/marshall/`.

The Dockerfile is at the base of the source code directory (see link below to download the source directory separately). To build a docker image from the Dockerfile, run from the base of the source directory the command
```
docker build --tag=marshallb .
```

#### Installing from source

First, download the source code.
[TODO] Source code

Install the following dependencies:
- rlwrap (we use version 0.43)
- MPFR (we use version 4.0.1)
- OPAM 2 (we use version 2.0.4), with an OPAM switch for OCaml 4.04.0.

Then, go to the base source directory, and run `opam install .`.

`marshall` should now be available as a command-line program.


### A quick evaluation

Run the shell script `examples/icfp/quick/run.sh`, which runs simplified (computationally less-expensive) versions of computations reported in case studies in sections 2, 8.1, and 8.2. It should take under 2 minutes to run. It diffs the generated outputs with expected outputs that are in that directory, so you should expect to see no output; any output will show a difference in the generated results from the expected ones. See Step-By-Step instructions for more thorough explanation of what these computations are. To verify the actual computations reported in the paper, run `examples/icfp/full/run.sh`, but be warned that this takes us 3.5-4 hours to run.

If you've completed this, then you have completed the "Getting Started" part of this artifact!

## Step-by-step instructions

Follow these instructions for a more thorough description of the artifact and files in the source directory.

### Artifact evaluation components

Our artifact consists of the following:

1. The MarshallB programming system, a programming language interpreter written in OCaml. Once MarshallB is installed, run `marshall` to open a REPL (Ctrl-D to exit), or pass as a command-line argument the filename of a MarshallB code file (suffix `.asd`) to process that file in its entirety.
2. The StoneWorks library for MarshallB, which is several files of MarshallB code located in `examples/stoneworks/`. To load the entire library at the REPL, run `#use "examples/stoneworks/cad.asd"`.
3. Standalone MarshallB files and commands to execute the case studies from the paper sections 2, 8.1, and 8.2, located at `examples/icfp/`. The executable shell script `examples/icfp/full/run.sh` runs each of the 4 computations (mentioned above), and compares the generated output with the expected output, which is included. Using a 3.1 GHz Core i7 (I7-7920HQ) CPU, this takes under 4 hours in total. There are less expensive versions of each of these computations in the `examples/icfp/quick` directory, which take under 2 minutes in total.

### Source code contents and thorough descriptions

Relative to the base of the source directory:
- `src/` contains the OCaml code for the `marshall` program that implements the interpreter for MarshallB.
- `examples/` contains libraries of MarshallB code.
- `examples/stoneworks/` contains the Stoneworks library for solid modeling.
  * `examples/stoneworks/orep.asd` provides a module for open representation (corresponding to Fig. 12)
  * `examples/stoneworks/krep.asd` provides a module for compact representation (corresponding to Fig. 13)
  * `examples/stoneworks/okrep.asd` provides a module for open-compact representation (corresponding to Fig. 14)
  * `examples/stoneworks/cad.asd` loads the entire Stoneworks library.
- `examples/icfp/` contains code for various case studies in the paper:
  * `examples/icfp/cam_piston.asd` defines the cam-piston system in Section 2.
  * `examples/icfp/ray_depth.asd` defines the ray depth intersection code and ball-table scene from Section 8.1.
  * `examples/icfp/mesh.asd` defines the mesh verification example of Section 8.2.
- `examples/icfp/full/` contains code for running actual computations whose results are described in the paper. On each of the following files, running `marshall FILE` should produce as command-line output the output `FILE.expected_out`. For each example, we point out the key part of the expected output, as well as an estimate of running time and maximum resident set size (memory usage). These are:
  * `examples/icfp/full/collision_safe.asd`: Section 2. Runtime: 0.4 seconds. Max resident set size: 8 MB. Produces as its last line `- : prop = True`, indicating that `collision_safe` returns `True`.
  * `examples/icfp/full/ball_table_image.asd`: Section 8.1. Runtime: 2 hours and 25 minutes. Max resident set size: 14 MB. Produces the 256x256 bitmap image `examples/icfp/full/ball_table.bmp`, which should be the same as `examples/icfp/full/ball_table.bmp.exepected`. Monotone adjustments to the brightness of the image (to make the depth more apparent) would result in the image shown in Fig. 16 of the paper.
  * `examples/icfp/full/mesh_lt.asd`: Section 8.2. Runtime: 30 minutes. Max resident set size: 155 MB. Produces as its last line `- : prop = True`, indicating that `hausdorff3 cone cone_mesh < 0.1` returns `True`.
  * `examples/icfp/full/mesh_gt.asd`: Section 8.2. Runtime: 36 minutes. Max resident set size: 398 MB. Produces as its last line `- : prop = True`, indicating that `hausdorff3 cone cone_mesh > 0.07` returns `True`.
- `examples/icfp/quick` contains code for running less expensive version of the computations from `examples/icfp/full` above. Running all of these computations should take less than 2 minutes in total (and under 20 MB memory).
  * `examples/icfp/quick/collision_safe.asd`: Same as full.
  * `examples/icfp/quick/ball_table_image.asd`: Runtime: 35 seconds. Max resident set size: 15 MB. Produces as 16x16 image, rather than a 256x256 image.
  * `examples/icfp/quick/mesh_lt.asd`: Runtime: 48 seconds. Max resident set size: 14 MB. Computes an upper bound of 0.4, rather than 0.1.
  * `examples/icfp/quick/mesh_gt.asd`: Runtime: 25 seconds. Max resident set size: 14 MB. Computes an lower bound of 0.02, rather than 0.07.

## Notes

### System requirements

All computations for the full case studies should run with under 400 MB of memory.

### Viewing and editing .asd files

In the base source code directory, the `marshall-mode.el` Emacs Lisp file defines an Emacs major mode for editing MarshallB code files ending in `.asd`, and providing the syntax highlighting and prettification that is present in the paper.