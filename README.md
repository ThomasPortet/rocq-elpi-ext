# Tactics deep_ring and deep_field

## Motivation
  The aim is to provide tactics in the spirit of ring and field, but which also
  work when the simplifiable expressions appear as arguments of functions that
  are not part of the ring or field language.

## How to compile and run

- You should create an opam switch with 
  rocq-core 9.2
  rocq-elpi 3.4.0
  vsrocq-language-server 2.5.0

- You should move the stdlib directory from this directory to a sibling
  directory (so that, from this directory, ../stdlib/theories is a valid path

- You should cd to the stdlib directory and type the following commnand

    make

  this compilation should take about a minute

- You should then cd back to this directory and type

  dune build

- if all compilations succeeded, you should just step through the file
  examples.v to see how the tactics we define work.