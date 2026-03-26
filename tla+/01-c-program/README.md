The example from the first example in the TLA+ tutorial videos,
of a little C program that picks a random number and increments
it.

The most interesting thing to do with this is to just view a
sample run:
```
tlc 01-c-program/c_program.tla -simulate -depth 3
```

I'm still not sure how to use tlc simulation mode well, but you
can use it to see some sample traces; in this sense it is a bit
similar to the alloy visualizer.
