These are my notes on how I got TLA+ up-and-running in a quick
and dirty way on a macbook; I usually try to have reproducible
installs (e.g. with nix) but I don't yet have this for TLA+.

I use VS Code with TLA+ rather than the toolbox; I find the toolbox
uncomfortable both becausee it's not a great editor and because it
hides some things I'd rather handle in plain text config file format
with a GUI.

The TLA+ extension from the TLA+ Foundation is the right tool for this.

You can get TLA+ command-line tools by running the install as described
in https://github.com/pmer/tla-bin.git.

I didn't have java enabled on this machine prior to installing TLA+, I
used `brew install java` to get it (brew uses openjdk by default) which
worked fine, although you do have to run a linking command that brew
spits out before the system `java` can find the brew-provided jdk.

I'm actually not 100% certain whether the VS Code extension uses these
binaries, or instead somehow integrates with the toolbox app because I
did also separately download the toolbox zip file and install the App
on my macos machine.

On a new machine, my suggestion would be to try just the binary download first
but I haven't yet tried it.
