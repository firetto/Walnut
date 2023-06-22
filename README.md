# Walnut
Walnut is an automated theorem prover for automatic words.

To run Walnut, first run "build.sh" to build Walnut, then run the "walnut.sh" file.

Please read the `Manual.pdf` file, included in the repository, to learn what Walnut is and how one would work with it. 

To run Walnut tests, run "build.sh" with the "-t" flag.

# WALNUT 6 Additional Documentation

This new version of Walnut has new capabilities and changes added by Anatoly Zavyalov (anatoly.zavyalov@mail.utoronto.ca), with direction from Jeffrey Shallit (shallit@uwaterloo.ca). This version also features major performance improvements by John Nicol.

The new capabilities are as follows:

- Automata operations
- Fixing leading and trailing zeroes
- Delimiters for Word Automata
- Reversing automata
- Bug fixes and performance improvements


# Automata operations

One can now perform basic automata operations. The operations, along with their commands, are:

 - Union of automata, using the `union` command
 - Intersection of automata, using the `intersect` command
 - Kleene star of automata, using the `star` command
 - Concatenation of automata, using the `concat` command
 
 
## Union of automata

The syntax for the `union` command is as follows:

```
union <new> <old1> [old2] [old3] ... [oldN]
```

The `union` command requires at least one input automaton. All automata must have the same input alphabet.

For example, to take the union `res` of automata named `a1` and `a2` both saved in `Automata Library/`, one uses the following command:
```
union res a1 a2;
```
The resulting automaton `res` is saved in `Automata Library/`, and accepts the union of the inputs accepted by `a1` and `a2`.


## Intersection of automata

The syntax for the `intersect` command is as follows:

```
union <new> <old1> [old2] [old3] ... [oldN]
```

The `intersect` command requires at least one input automaton. All automata must have the same input alphabet.

For example, to take the intersection `res` of automata named `a1` and `a2` both saved in `Automata Library/`, one uses the following command:
```
intersect res a1 a2;
```
The resulting automaton `res` is saved in `Automata Library/`, and accepts the intersection of the inputs accepted by `a1` and `a2`.


## Kleene star of automata

The syntax for the `star` command is as follows:
```
star <new> <old>
```
For example, to take the Kleene star `res` of the automaton `aut` saved in `Automata Library/`, one uses the following command:
```
star res aut;
```
The resulting automaton `res` is saved in `Automata Library/`, and accepts the Kleene star of the inputs accepted by `aut`.

NOTE: The resulting automaton `res` will be defined on the exact set of inputs that `aut` is defined on. For example, if `aut` is an `msd_fib` automaton and accepts on an input of `1`, `res` will be undefined on an input of `11` instead of accepting.


## Concatenation of automata

The syntax for the `concat` command is as follows:
```
concat <new> <old1> <old2> [old3] ... [oldN]
```
The `concat` command requires at least two input automata. All automata must have the same input alphabet.

For example, to take the concatenation `res` of automata named `a1`, `a2`, `a3` and `a4`, all saved in `Automata Library/`, one uses the following command:
```
concat res a1 a2 a3 a4;
```
The resulting automaton `res` is saved in `Automata Library/`, and accepts the concatenation of the inputs accepted by `a1`, `a2`, `a3`, and `a4`.

NOTE: The resulting automaton `res` will be defined on the exact set of inputs that the old automata are defined on. For example, if `a1` and `a2` are `msd_fib` automata and accepts on an input of `1`, and `res` is the concatenation of `a1` and `a2`, then `res` will be undefined on an input of `11` instead of accepting.



# Fixing leading and trailing zeroes

One can now "fix" leading and trailing zeroes for Automata (not Word Automata) using the "fixleadzero" and "fixtrailzero" commands. The syntax is as follows: for an automaton "foo" saved in "Automata Library/", one writes

	fixleadzero bar foo;

The resulting automaton bar accepts an input 0* x' if and only if foo accepts an input x, where x' is x with its leading zeroes removed.


Similarly, for trailing zeroes, one writes

	fixtrailzero bar foo;

The resulting automaton bar accepts an input x' 0* if and only if foo accepts an input x, where x' is x with its trailing zeroes removed.


For both cases, the resulting automaton "bar" will be saved in the "Automata Library/" directory.



# Delimiters for Word Automata

In previous versions of Walnut, word automata names could not begin with A, E, or I. This restriction has now been lifted using a new delimiter for word automata: putting "." (without quotation marks) before the name of a word automaton now signals that the following string of characters is the name of the word automaton. 

If there is a word automaton named AUTOMATON, you can write ".AUTOMATON" (without quotation marks) to refer to it in eval/def commands. For example, the following is now valid:

    def test ".AUTOMATON[n] = @1";



# Reversing automata

One can now use the "reverse" command to reverse ordinary automata saved in the "Automata Library/" directory.

To reverse Automata, one prepends the "$" symbol (without the quotation marks) to the old Automaton's name. The result will be saved in the "Automata Library/" directory.

For example, to reverse an Automaton named "foo" saved in "Automata Library/", one writes

	reverse bar $foo;

The resulting automaton bar will be saved in "Automata Library/".



# Bug fixes

- Fixed a bug where the resulting Word Automaton after running the "combine" command was not totalized
- Fixed a bug where reversing an automaton that does not have a number system (i.e. uses {0, 1} as a number system) will throw an error
- Fixed a bug where whitespace and new lines in regular expressions could result in differing automata



# Performance improvements
- Significant memory and time improvements; thanks to John Nicol for their contributions!
- Multiplication has been drastically sped up