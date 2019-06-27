# assorted-tamari

Sagemath codes for various Tamari-related objects

## Contents

- `nu_tamari_lattice.py`: a function that returns a generalized Tamari lattice indexed by a directed path

- `lactree.py`: a class of LAC-trees defined in [The Steep-Bounce Zeta Map in Parabolic Cataland](https://arxiv.org/abs/1903.08515), with bijections to
  
  * bounce pairs
  * steep pairs
  * walks in quadrant
  
  A functionality of (exponential time) random generation is also provided. Scale up little by little when using it!

## Usage

There is minimal documentation in the code, explaining the input and the output of each function. This is mostly for internal use for the moment...

To use them in a Jupyter notebook, simply use the `load()` command.

Good luck!

## TODO

- Add more objects (alpha-non-crossing partitions)
