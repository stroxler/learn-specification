# A Nix flake for alloy6


Unfortunately, it seems like `--help` doesn't work well. But the important commands are these:

# commands

```
alloy6 commands <filename>
```
to see the commands (`run` and `check` predicates).


# exec
```
alloy6 exec \
  -o .traces -f \
  -r 50 \
  -t json \
  <filename>
```
where:
- `-o` is the output directory, I like `.traces` as a default
- `-f` says to overwrite the directory if it exists already
- `-r` is the number of runs, often 50 is a decent default. You can use -0 to view all
  but in many cases this is a huge space and you don't really want that many traces;
  it's usually better to tighten up the command predicate to that the first 50 hits are
  interesting.
- `-t` gives the output type; `json` is good for writing scripts to consume the traces
  but other options include `text` (compact but hard to read), `table` (readable but big)
  and `xml`

My current opinion is that with agents, a lot of productivity is likely to come from
writing model-specific scripts to visualize traces as text - this is great for agents,
and actually seems pretty useful even for me, I can emulate the experience of a TLA
trace which is nice.

That said, visualization is a core advantage of Alloy and I need to figure out
how to get the most from this. I think that [Sterling](https://sterling-js.github.io/)
is almost certainly going to be the best path forward for me rather than the built
in visualizer, for two reasons:
- First, I'm pretty interested in running alloy on remote machines in a corporate
  environment, in which case the UI isn't much of an option but a web UI viewable
  over an SSH tunnel is
- Second, I suspect that - as with using custom per-model scripts to view traces
  in the command line - custom visualizations can be a superpower for Alloy models,
  and Sterling seems to make it much easier to customize. Agents can probably
  help make these customizations much more easily than you could before, so building
  around a tool that makes this easy could be great.

It might also be worth considering the extent to which a terminal UI could be used
for visualizing, which could have some UX advantages if we can make it pretty enough.
But that seems like a question for later (and in some ways just an extension of the
scripting / pretty printing approach).
