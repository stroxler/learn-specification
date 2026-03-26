# Model of a Pyrefly stack

Using the Alloy CLI isn't documented much, most people focus on using the analyzer GUI,
which is relatively user friendly but I want to focus on the CLI for a variety of reasons,
including the ability to do some development remotely.

You can view available commands with
```
alloy commands pyrefly_stack.als
```

Assuming that `show` is the first command (a command is either a `run` or a `check` predicate),
you can collect traces with
```
N=50
rm -rf .traces && alloy exec -c 0 -o .traces -t json -r $N pyrefly_stack.als
```
Here `$N` / `-r` is the number of traces to collect; it's fairly slow to get huge numbers
of traces so you likely want to play with restricting the predicate on `show` if you want
to explore a large space, although you certainly can run it in-the-large if you really want;
using `-r 0` will give you a "full state space" run, but the output will be huge.

Output then shows up in `.traces` as `show-solution-<n>.json` dumps. You can visualize
a trace using `trace_summary.py`, e.g.
```
python3 trace_summary.py .traces/show-solution-10.json
```

You can use the `-o` flag to set a different output directory if you want to analyze
multiple sets of traces, the commands above are geared toward looking at just one trace.
The json traces aren't easy to read; you could use raw text traces to get a more
compact view, but json is better for pretty-printing trace information (as we are doing
with `trace_summary.py`
