# Walnut
Walnut is an automated theorem prover for automatic words.

Please read the `Manual.pdf` file, included in the repository, to learn what Walnut is and how one would work with it. 

# Walnut 5 Documentation

This new version of Walnut has new capabilities and changes added by Anatoly Zavyalov, with direction from Jeffrey Shallit.

The new capabilities are as follows:

1.	Transducing k-automatic sequences
2. Converting number systems
3. Reversing word automata
4. Minimizing word automata
5. Changes to the reversal (`` ` ``) operation
6. Improvements to logging
7. Bug fixes

## 1. Transducing k-automatic sequences

One may now transduce automata (that have at most one edge per input per two states) with the following syntax:

```
transduce <new> <TRANSDUCER> <old>
```

For example, to transduce a word automaton `T` saved in `Word Automata Library/T.txt` using a transducer named `RUNSUM2` saved in `Transducer Library/RUNSUM2.txt`, one writes the following:

```
transduce new_T RUNSUM2 T;
```

The above command saves a new word automaton `new_T` in the directory `Word Automata Library/`.

To transduce automata saved in `Automata Library/`, one may add a prefix of `$` to the automaton name. For example, if trying to transduce the automaton `xda` saved in `Automata Library/xda.txt` using a transducer named `RUNSUM2` saved in `Transducer Library/RUNSUM2.txt`, one writes the following:

```transduce another_T RUNSUM2 $xda;```

The above command will save a new word automaton `another_T` in the directory Word Automata Library/.

To define a transducer, create a `.txt` file in the `Transducer Library/` folder in the Walnut directory with the desired name of the transducer. Transducers are defined similarly to automata, with the exception of an output at the end of each transition. The accepted format for writing transitions is as follows:

````<input> -> <new state> / <output>````

Below is an example transducer definition with three states, computing the XOR of adjacent bits in a sequence over `{0, 1}` (with the first output always being 0):

```
# XOR.txt

{0, 1}

0
0 -> 1 / 0
1 -> 2 / 0

1
0 -> 1 / 0
1 -> 2 / 1

2
0 -> 1 / 1
1 -> 2 / 0
```

## 2. Converting number systems

One may now convert the number system of an Automaton or a Word Automaton with one input from a base of k^i to /k^j, where k, i and j are positive integers with k >= 2. Note that this allows for conversions from msd to lsd, lsd to msd and vice versa, and lsd to lsd. The following syntax is used:

```
convert <new> <numberSystem> <old>
```

For example, to transduce a Word Automaton `T` saved in `Word Automata Library/T.txt` to `msd_8` (assuming `T` is in `msd_2`), one runs:

```convert T_new msd_8 T;```

The above command will save a new word automaton `T_new` in the directory `Word Automata Library/`.

To convert the number system of an Automaton saved in `Automata Library/`, one may add a prefix of `$` to the old automaton's name. For example, if trying to convert the Automaton `quag` saved in `Automata Library/quag.txt` from `msd_2` to `lsd_16` and save it as a Word Automaton, one runs:

```convert quag_new lsd_16 $quag;```

The above command will save a new word automaton `quag_new` in the directory `Word Automata Library/`.

If the resulting base of the new automaton is 2 (that is, the new number system is either msd_2 or lsd_2), then one may save the resulting automaton as an Automaton in the Automata Library/ directory, by adding a prefix of `$` to the new automaton's name. For example, if `elephant` is a Word Automaton over the number system `lsd_32`, one can run:

```convert $elephant_new msd_2 elephant;```

The above command will save a new automaton `elephant_new` in the directory `Automata Library/`.

## 3. Reversing word automata

One may now reverse a Word Automaton, with the following syntax:

```reverse <new> <old>```

**NOTE**: Reversing an automaton will flip the number system from msd to lsd, and vice versa.

For example, if reversing a word automaton `DEJ` saved in `Word Automata Library/DEJ.txt` with a number system of `msd_19`, one runs:

```reverse DEJ_new DEJ;```

`DEJ_new` will be a Word Automaton that is the reverse of `DEJ`, with a number system of `lsd_19`, and will be saved in `Word Automata Library/`.

**NOTE**: To reverse Automata (those saved in `Automata Library/`), use the already existing `` ` `` operation.

## 4. Minimizing word automata

One may now minimize a Word Automaton, with the following syntax:

```minimize <new> <old>```

For example, if minimizing a word automaton `NOTMIN` saved in `Word Automata Library/NOTMIN.txt`, one runs:

```minimize MIN NOTMIN;```

`MIN` will be a minimal Word Automaton equivalent to `NOTMIN`, and will be saved in `Word Automata Library/`.

## 5. Changes to the reversal `` ` `` operation

Reversing an automaton using the `` ` `` operation will now change its number system(s) from msd to lsd, and vice versa.

## 6. Improvements to logging

Commands that involve determinizing or taking the cross product of automata that are ran with the `:` or `::` suffices (without the quotation marks) will now include further logging that update the user on how many states have been added so far, how many states remain in the queue, and how many states have been reached in total so far.

## 7. Bug fixes

- Fixed bug that prevented subset construction of automata with large amounts of states in certain cases.
- Fixed bug that did not allow to combine automata with negative integer outputs.
- Fixed bug that produced incorrect automata when defining regular expressions with negative integers.
