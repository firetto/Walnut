/*   Copyright 2022 Anatoly Zavyalov
 *
 *   This file is part of Walnut.
 *
 *   Walnut is free software: you can redistribute it and/or modify
 *   it under the terms of the GNU General Public License as published by
 *   the Free Software Foundation, either version 3 of the License, or
 *   (at your option) any later version.
 *
 *   Walnut is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU General Public License for more details.
 *
 *   You should have received a copy of the GNU General Public License
 *   along with Walnut.  If not, see <http://www.gnu.org/licenses/>.
 */

package Automata;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.TreeMap;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.Iterator;

import java.lang.Math;

import Main.UtilityMethods;
import it.unimi.dsi.fastutil.ints.Int2ObjectRBTreeMap;
import it.unimi.dsi.fastutil.ints.IntArrayList;
import it.unimi.dsi.fastutil.ints.IntList;

/**
 * The class Transducer represents a deterministic finite-state transducer with all states final that is 1-uniform.
 * <p>
 * It is implemented by constructing a deterministic finite-state automaton with all states final, and adding on top a
 * 1-uniform output function with the domain S x A (where S is the set of states and A is the input alphabet),
 * and the codomain being an output alphabet (subset of the integers).
 *
 * @author Anatoly
 */
public class Transducer extends Automaton {


    /**
     * Output function for the Transducer.
     * For example, when sigma[0] = [(0, 1), (1, 0), (2, -1), (3, 2), (4, -1), (5, 3)]
     * and input alphabet A = [[0, 1], [-1, 2, 3]],
     * then from state 0 on
     * (0, -1) we output 1
     * (0, 2) we output 0
     * (0, 3) we output -1
     * (1, -1) we output 2
     * (1, 2) we output -1
     * (1, 3) we output 3
     *
     * Just like in an Automaton's transition function d, we store the encoded values of inputs in sigma, so instead of
     * saying that "on (0, -1) we output 1", we really store "on 0, output 1".
     */
    public List<TreeMap<Integer, Integer>> sigma;

    /**
     * Default constructor for Transducer. Calls the default constructor for Automaton.
      */
    public Transducer() {
        super();

        sigma = new ArrayList<>();
    }

    /**
     * Takes an address and constructs the transducer represented by the file referred to by the address.
     * @param address
     * @throws Exception
     */
    public Transducer(String address) throws Exception {
        this();
        final String REGEXP_FOR_WHITESPACE = "^\\s*$";

        // lineNumber will be used in error messages
        int lineNumber = 0;

        alphabetSize = 1;

        try {
            BufferedReader in = new BufferedReader(
                    new InputStreamReader(new FileInputStream(address), "utf-8"));
            String line;
            while ((line = in.readLine()) != null) {
                lineNumber++;

                if (line.matches(REGEXP_FOR_WHITESPACE)) {
                    // Ignore blank lines.
                    continue;
                }
                else {
                    boolean flag = false;
                    try {
                        flag = ParseMethods.parseAlphabetDeclaration(line, A, NS);

                    } catch (Exception e) {
                        in.close();
                        throw new Exception(
                                e.getMessage() + UtilityMethods.newLine() +
                                        "\t:line "+ lineNumber + " of file " + address);
                    }

                    if (flag) {
                        for (int i = 0; i < A.size(); i++) {
                            if(NS.get(i) != null &&
                                    (!A.get(i).contains(0) || !A.get(i).contains(1))) {
                                in.close();
                                throw new Exception(
                                        "The " + (i + 1) + "th input of type arithmetic " +
                                                "of the automaton declared in file " + address +
                                                " requires 0 and 1 in its input alphabet: line " +
                                                lineNumber);
                            }
                            UtilityMethods.removeDuplicates(A.get(i));
                            alphabetSize *= A.get(i).size();
                        }

                        break;
                    }
                    else {
                        in.close();
                        throw new Exception(
                            "Undefined statement: line " +
                            lineNumber + " of file " + address);
                    }
                }
            }

            int[] singleton = new int[1];
            List<Integer> input = new ArrayList<>();
            IntList dest = new IntArrayList();
            List<Integer> output = new ArrayList<>();
            int currentState = -1;
            int currentStateOutput;
            Int2ObjectRBTreeMap<IntList> currentStateTransitions = new Int2ObjectRBTreeMap<>();
            TreeMap<Integer, Integer> currentStateTransitionOutputs = new TreeMap<>();
            TreeMap<Integer,Integer> state_output = new TreeMap<>();
            TreeMap<Integer, Int2ObjectRBTreeMap<IntList>> state_transition =
                    new TreeMap<>();
            TreeMap<Integer, TreeMap<Integer, Integer>> state_transition_output =
                    new TreeMap<>();
            /**
             * This will hold all states that are destination of some transition.
             * Then we make sure all these states are declared.
             */
            Set<Integer> setOfDestinationStates = new HashSet<>();
            Q = 0;
            while((line = in.readLine())!= null) {
                lineNumber++;
                if(line.matches(REGEXP_FOR_WHITESPACE)) {

                    continue;
                }

                if(ParseMethods.parseTransducerStateDeclaration(line, singleton)) {
                    Q++;
                    if(currentState == -1) {
                        q0 = singleton[0];
                    }

                    currentState = singleton[0];
                    currentStateOutput = 0; // state output does not matter for transducers.
                    state_output.put(currentState, currentStateOutput);
                    currentStateTransitions = new Int2ObjectRBTreeMap<>();
                    state_transition.put(currentState, currentStateTransitions);
                    currentStateTransitionOutputs = new TreeMap<>();
                    state_transition_output.put(currentState, currentStateTransitionOutputs);
                } else if(ParseMethods.parseTransducerTransition(line, input, dest, output)) {
                    setOfDestinationStates.addAll(dest);

                    if(currentState == -1){
                        in.close();
                        throw new Exception(
                                "Must declare a state before declaring a list of transitions: line " +
                                        lineNumber + " of file " + address);
                    }

                    if(input.size() != A.size()) {
                        in.close();
                        throw new Exception("This automaton requires a " + A.size() +
                                "-tuple as input: line " + lineNumber + " of file " + address);
                    }
                    List<List<Integer>> inputs = expandWildcard(input);

                    for(List<Integer> i : inputs) {
                        currentStateTransitions.put(encode(i), dest);
                        if (output.size() == 1) {
                            currentStateTransitionOutputs.put(encode(i), output.get(0));
                        }
                        else {
                            in.close();
                            throw new Exception("Transducers must have one output for each transition: line "
                                    + lineNumber + " of file " + address);
                        }
                    }

                    input = new ArrayList<>();
                    dest = new IntArrayList();
                    output = new ArrayList<>();
                }
                else{
                    in.close();
                    throw new Exception("Undefined statement: line "+ lineNumber + " of file " + address);
                }
            }
            in.close();
            for(int q:setOfDestinationStates) {
                if(!state_output.containsKey(q)) {
                    throw new Exception(
                            "State " + q + " is used but never declared anywhere in file: " + address);
                }
            }

            for(int q = 0; q < Q; q++) {
                O.add((int)state_output.get(q));
                d.add(state_transition.get(q));
                sigma.add(state_transition_output.get(q));
            }

        } catch (IOException e) {
            e.printStackTrace();
            throw new Exception("File does not exist: " + address);
        }
    }

    /**
     * Returns a deep copy of this transducer.
     */
    public Transducer clone() {
        Transducer T = new Transducer();
        T.Q = Q;
        T.q0 = q0;
        T.alphabetSize = alphabetSize;
        T.canonized = canonized;
        T.labelSorted = labelSorted;
        for(int i = 0 ; i < A.size();i++){
            T.A.add(new ArrayList<>(A.get(i)));
            T.NS.add(NS.get(i));
            if(encoder != null && encoder.size()>0){
                if(T.encoder == null) T.encoder = new ArrayList<>();
                T.encoder.add(encoder.get(i));
            }
            if(label != null && label.size() == A.size())
                T.label.add(label.get(i));
        }
        for(int q = 0; q < Q; q++){
            T.O.add(O.getInt(q));
            T.d.add(new Int2ObjectRBTreeMap<>());
            for(int x:d.get(q).keySet()){
                T.d.get(q).put(x, new IntArrayList(d.get(q).get(x)));
            }
        }
        for (int i = 0; i < sigma.size(); i++) {
            T.sigma.add(new TreeMap<>(sigma.get(i)));
        }
        return T;
    }

    /**
     * Transduce an msd-k Automaton M as in Dekking (1994).
     *
     * @param M - automaton to transduce
     * @param print - whether to print details
     * @param prefix - prefix for printing details
     * @param log - log to write the details to
     * @return The transduced Automaton after applying this Transducer to M.
     * @throws Exception
     */
    public Automaton transduceMsdDeterministic(Automaton M, boolean print, String prefix, StringBuilder log) throws Exception {

        try {
            long timeBefore = System.currentTimeMillis();
            if(print){
                String msg = prefix + "transducing: " + M.Q + " state automaton - " + Q + " state transducer";
                log.append(msg + UtilityMethods.newLine());
                System.out.println(msg);
            }

            

            /**
             * N will be the returned Automaton, just have to build it up.
             */
            Automaton N = new Automaton();

            // build up the automaton.
            for (int i = 0; i < M.A.size(); i++) {
                N.A.add(M.A.get(i));
                N.NS.add(M.NS.get(i));

                // Copy the encoder
                if (M.encoder != null && M.encoder.size() > 0) {
                    if (N.encoder == null) {
                        N.encoder = new ArrayList<>();
                    }
                    N.encoder.add(M.encoder.get(i));
                }

                // Copy the label
                if (M.label != null && M.label.size() == M.A.size()) {
                    N.label.add(M.label.get(i));
                }
            }

            // TODO: This probably should be configurable, and should not necessarily be 0.
            N.q0 = 0;

            /*
                Need to find P and Q so the transition function of the Transducer becomes ultimately periodic with lag Q
                and period P.
             */

            int p, q;

            // Will be used for hashing the iterate maps.
            HashMap<List<Map<Integer, Integer>>, Integer> iterateMapHash = new HashMap<>();

            // iterateStrings[i] will be a map from a state q of M to h^i(q).
            List<List<List<Integer>>> iterateStrings = new ArrayList<>();

            // initMaps.get(i) will be the map phi_{M.O(i)}
            List<Map<Integer, Integer>> initMaps = new ArrayList<>();

            // initStrings.get(j) = [j];
            List<List<Integer>> initStrings = new ArrayList<>();

            // start with the empty string.
            HashMap<Integer, Integer> identity = new HashMap<>();

            // identity will be the identity, so we want to iterate through the states of the transducer.
            for (int i = 0; i < Q; i++) {
                identity.put(i, i);
            }

            // will add M.Q maps to initMaps.
            for (int i = 0; i < M.Q; i++) {

                HashMap<Integer, Integer> map = new HashMap<>();

                for (int j = 0; j < Q; j++) {
                    map.put(j, d.get(j).get( encode(Arrays.asList(M.O.getInt(i))) ).getInt(0));
                }

                initMaps.add(map);

                initStrings.add(Arrays.asList(i));
            }

            iterateMapHash.put(initMaps, 0);


            iterateStrings.add(initStrings);

            int mFound = -1, nFound = -1;

            for (int m = 1; ; m++) {

                List<List<Integer>> prevStrings = iterateStrings.get(iterateStrings.size() - 1);

                List<Map<Integer, Integer>> newMaps = new ArrayList<>();

                List<List<Integer>> newStrings = new ArrayList<>();

                for (int i = 0; i < M.Q; i++) {

                    // will be h^m(i)
                    List<Integer> iString = new ArrayList<>();

                    for (int u = 0; u < prevStrings.get(i).size(); u++) {

                        // for every digit in the alphabet of M
                        for (int l : M.d.get(prevStrings.get(i).get(u)).keySet()) {

                            // each list of states that this transition goes to.
                            // we assuming it's a DFA for now, so this has length 1 we're assuming...

                            // get the first index of M.d on state x and edge label l

                            iString.add(M.d.get(prevStrings.get(i).get(u)).get(l).getInt(0));
                        }
                    }

                    newStrings.add(iString);

                    // start off with the identity.
                    HashMap<Integer, Integer> mapSoFar = new HashMap<>(identity);

                    for (int u = 0; u < iString.size(); u++) {
                        HashMap<Integer, Integer> newMap = new HashMap<>();
                        for (int l = 0; l < Q; l++) {
                            newMap.put(l, d.get(mapSoFar.get(l)).get( encode(Arrays.asList(M.O.getInt(iString.get(u)))) ).getInt(0));
                        }
                        mapSoFar = newMap;
                    }

                    newMaps.add(mapSoFar);

                }

                iterateStrings.add(newStrings);

                if (iterateMapHash.containsKey(newMaps)) {
                    nFound = iterateMapHash.get(newMaps);
                    mFound = m;
                }
                else {
                    iterateMapHash.put(newMaps, m);
                }

                if (mFound != -1) {
                    break;
                }

            }

            p = mFound - nFound;
            q = nFound;

        /*
            Make the states of the automaton.
         */

            // now to generate the actual states.

            N.q0 = 0;

            // tuple of the form (a, iters) where iters is a list of p+q maps phi_{M.O(w)}, ..., phi_{h^{p+q-1}(M.O(W))}
            class StateTuple {
                final int state;
                final List<Integer> string;
                final List<Map<Integer, Integer>> iterates;
                StateTuple(int state, List<Integer> string, List<Map<Integer, Integer>> iterates) {
                    this.state = state;
                    this.string = string;
                    this.iterates = iterates;
                }

                @Override
                public boolean equals(Object o) {

                    // DO NOT compare the string.
                    if (this == o) {
                        return true;
                    }
                    if (o == null || this.getClass() != o.getClass()) {
                        return false;
                    }
                    StateTuple other = (StateTuple) o;
                    if (this.state != other.state) {
                        return false;
                    }

                    if (this.iterates.size() != other.iterates.size()) {
                        return false;
                    }
                    for (int i = 0; i < this.iterates.size(); i++) {
                        if (!this.iterates.get(i).equals(other.iterates.get(i))) {
                            return false;
                        }
                    }
                    return true;
                }

                @Override
                public int hashCode() {

                    // DO NOT use the string to hash. Only use the state and the iterates.
                    int result = this.state ^ (this.state >>> 32);
                    result = 31 * result + this.iterates.hashCode();
                    return result;
                }
            }

            ArrayList<StateTuple> states = new ArrayList<>();

            HashMap<StateTuple, Integer> statesHash = new HashMap<>();

            Queue<StateTuple> statesQueue = new LinkedList<>();

            StateTuple initState = new StateTuple(M.q0, Arrays.asList(), createIterates(M, Arrays.asList(), p+q));

            states.add(initState);

            statesHash.put(initState, states.size() - 1);

            statesQueue.add(initState);

            while (statesQueue.size() > 0) {
                StateTuple currState = statesQueue.remove();

                // set up the output of this state.

                N.O.add((int)sigma.get(currState.iterates.get(0).get(q0)).get( encode(Arrays.asList(M.O.getInt(currState.state))) ));

                N.d.add(new Int2ObjectRBTreeMap<>());

                // get h(w) where w = currState.string .
                List<Integer> newString = new ArrayList<>();

                for (int u = 0; u < currState.string.size(); u++) {

                    // for every digit in the alphabet of M
                    for (int l : M.d.get(currState.string.get(u)).keySet()) {

                        // each list of states that this transition goes to.
                        // we assuming it's a DFA for now, so this has length 1 we're assuming...

                        // get the first index of M.d on state x and edge label l

                        newString.add(M.d.get(currState.string.get(u)).get(l).getInt(0));
                    }
                }

                List<Integer> stateMorphed = new ArrayList<>();

                // relying on the di's to be sorted here...
                for (int di : M.d.get(currState.state).keySet()) {
                    stateMorphed.add(M.d.get(currState.state).get(di).getInt(0));
                }

                // look at all of the states that this state transitions to.
                for (int di : M.d.get(currState.state).keySet()) {
                    // make new state string
                    List<Integer> newStateString = new ArrayList<>(newString);
                    for (int u = 0; u < di; u++) {
                        newStateString.add(stateMorphed.get(u));
                    }

                    // new state
                    StateTuple newState = new StateTuple(
                            stateMorphed.get(di),
                            newStateString,
                            createIterates(M, newStateString, p+q)
                    );

                    // check if the state is already hashed.
                    if (!statesHash.containsKey(newState)) {
                        states.add(newState);
                        statesHash.put(newState, states.size() - 1);
                        statesQueue.add(newState);
                    }

                    // set up the transition.
                    IntList newList = new IntArrayList();
                    newList.add((int)statesHash.get(newState));
                    N.d.get(N.d.size() - 1).put(di, newList);
                }
            }

            N.Q = states.size();

            N.alphabetSize = M.alphabetSize;

            N.minimizeSelfWithOutput(print, prefix+" ", log);

            long timeAfter = System.currentTimeMillis();
            if(print){
                String msg = prefix + "transduced: " + N.Q + " states - "+(timeAfter-timeBefore)+"ms";
                log.append(msg + UtilityMethods.newLine());
                System.out.println(msg);
            }


            return N;
        } catch (Exception e) {
            e.printStackTrace();
            throw new Exception("Error transducing automaton");
        }

    }

    /**
     * Transduce an automaton that may have undefined transitions as in Dekking (1994). The automaton may not have
     * more than one transition per input character per state.
     *
     * @param M - automaton to transduce
     * @param print - whether to print details
     * @param prefix - prefix for printing details
     * @param log - log to write the details to
     * @return The transduced Automaton after applying this Transducer to M.
     * @throws Exception
     */
    public Automaton transduceNonDeterministic(Automaton M, boolean print, String prefix, StringBuilder log) throws Exception {

        // check that the input automaton only has one input!
        if (M.NS.size() != 1) {
            throw new Exception("Automata with only one input can be transduced.");
        }


        // Check that the output alphabet of the automaton is compatible with the input alphabet of the transducer.
        for (int i = 0; i < M.O.size(); i++) {
            int encoded = encode(Arrays.asList(M.O.getInt(i)));
            if (!d.get(0).containsKey(encoded)) {
                throw new Exception("Output alphabet of automaton must be compatible with the transducer input alphabet");
            }
        }

        // make sure the number system is lsd.
        boolean toLsd = false;

        if (!M.NS.get(0).isMsd()) {
            if(print){
                String msg = prefix + "Automaton number system is lsd, reversing";
                log.append(msg + UtilityMethods.newLine());
                System.out.println(msg);
            }
            toLsd = true;
            M.reverseWithOutput(true, print, prefix+" ", log);
        }


        // verify that the automaton is indeed nondeterministic, i.e. it has undefined transitions. If it is not, transduce normally.
        boolean totalized = true;
        for(int q = 0 ; q < M.Q; q++){
            for(int x = 0; x < M.alphabetSize; x++){
                if(!M.d.get(q).containsKey(x)) {
                    totalized = false;
                }
                else if (M.d.get(q).get(x).size() > 1) {
                    throw new Exception("Automaton must have at most one transition per input per state.");
                }
            }
        }
        Automaton N;
        if (totalized) {
            // transduce normally
            N = transduceMsdDeterministic(M, print, prefix, log);
        }
        else {
            Automaton Mnew = M.clone();
            Mnew.addDistinguishedDeadState(print, prefix+" ", log);

            // after transducing, all states with this minimum output will be removed.
            int minOutput = 0;
            if (Mnew.O.size() == 0) {
                throw new Exception("Output alphabet is empty");
            }
            for (int i = 0; i < Mnew.O.size(); i++) {
                if (Mnew.O.getInt(i) < minOutput) {
                    minOutput = Mnew.O.getInt(i);
                }
            }

            Transducer Tnew = clone();

            for (int q = 0; q < Tnew.Q; q++) {
                IntList newList = new IntArrayList();
                newList.add(q);
                Tnew.d.get(q).put(minOutput, newList);
                Tnew.sigma.get(q).put(minOutput, minOutput);
            }

            N = Tnew.transduceMsdDeterministic(Mnew, print, prefix+" ", log);

            // remove all states that have an output of minOutput
            HashSet<Integer> statesRemoved = new HashSet<>();

            for (int q = 0; q < N.Q; q++) {
                if (N.O.getInt(q) == minOutput) {
                    statesRemoved.add(q);
                }
            }
            for (int q = 0; q < N.Q; q++) {

                Iterator<Integer> iter = N.d.get(q).keySet().iterator();

                while (iter.hasNext()) {
                    int x = iter.next();

                    if (statesRemoved.contains(N.d.get(q).get(x).getInt(0))) {
                        iter.remove();
                    }
                }
            }

            N.canonized = false;
            N.canonize();
            
        }

        if (toLsd) {
            N.reverseWithOutput(true, print, prefix+" ", log);
        }

        return N;
    }

    /**
     * Take a string w of states of automaton M, and return the list
     *      [phi_{M.O(w)}, phi_{M.O(h(w))}, ..., phi_{M.O(h^{size - 1}(w))}]
     * where h is the morphism associated with M.
     * @param M - an Automaton to be transduced
     * @param string - a list of states of M
     * @param size - the size of the resulting list of maps.
     * @return
     */
    private List<Map<Integer, Integer>> createIterates(Automaton M, List<Integer> string, int size) {

        ArrayList<Map<Integer, Integer>> iterates = new ArrayList<>();
        // start with the empty string.
        HashMap<Integer, Integer> identity = new HashMap<>();

        // we want to iterate through the states of the transducer.
        for (int i = 0; i < Q; i++) {
            identity.put(i, i);
        }

        ArrayList<Integer> currString = new ArrayList<>(string);

        for (int i = 0; i < size; i++) {

            // make the map associated with currString and add it to the iterates array.

            // start off with the identity.
            HashMap<Integer, Integer> mapSoFar = new HashMap<>(identity);

            for (int u = 0; u < currString.size(); u++) {
                HashMap<Integer, Integer> newMap = new HashMap<>();
                for (int l = 0; l < Q; l++) {
                    newMap.put(l, d.get(mapSoFar.get(l)).get( encode(Arrays.asList(M.O.getInt(currString.get(u)))) ).getInt(0));
                }
                mapSoFar = newMap;
            }

            iterates.add(mapSoFar);

            // make new string currString to be h(currString), where h is the morphism associated with M.
            if (i != size - 1) {
                ArrayList<Integer> newString = new ArrayList<>();

                for (int u = 0; u < currString.size(); u++) {

                    // for every digit in the alphabet of M
                    for (int l : M.d.get(currString.get(u)).keySet()) {

                        // each list of states that this transition goes to.
                        // we assuming it's a DFA for now, so this has length 1 we're assuming...

                        // get the first index of M.d on state x and edge label l

                        newString.add(M.d.get(currString.get(u)).get(l).getInt(0));
                    }
                }
                currString = newString;
            }
        }

        return iterates;
    }


//    /**
//     * Writes down this transducer to a .gv file given by the address. It uses the predicate that
//     * caused this automaton as the label of this drawing.
//     * Unlike prior versions of Walnut, this automaton can be a non deterministic automaton and also a DFAO.
//     * In case of a DFAO the drawing contains state outputs with a slash (eg. "0/2" represents an output
//     * of 2 from state 0)
//     * @param address
//     */
//    public void draw(String address,String predicate) throws Exception{
//        GraphViz gv = new GraphViz();
//
//        canonize();
//        gv.addln(gv.start_graph());
//        gv.addln("label = \""+ UtilityMethods.toTuple(label) +": "+predicate+"\";");
//        gv.addln("rankdir = LR;");
//        for(int q = 0 ; q < Q;q++){
//            gv.addln("node [shape = circle, label=\""+q+"\", fontsize=12]"+q +";");
//        }
//
//        gv.addln("node [shape = point ]; qi");
//        gv.addln("qi -> " + q0+";");
//
//        TreeMap<Integer, TreeMap<Integer, List<String>>> transitions =
//                new TreeMap<>>>();
//        for(int q = 0; q < Q; q++) {
//            transitions.put(q, new TreeMap<>());
//            for(int x : d.get(q).keySet()) {
//                for(int dest : d.get(q).get(x)) {
//                    transitions.get(q).putIfAbsent(dest, new ArrayList<>());
//                    transitions.get(q).get(dest).add(
//                            UtilityMethods.toTransitionLabel(decode(x)));
//                }
//            }
//        }
//
//        for(int q = 0; q < Q; q++) {
//            for(int dest : transitions.get(q).keySet()) {
//                String transition_label = String.join(", ", transitions.get(q).get(dest)) +
//                        " / " + sigma.get(q).get(dest);
//                gv.addln(q + " -> " + dest + "[ label = \"" + transition_label + "\"];");
//            }
//        }
//
//        gv.addln(gv.end_graph());
//
//        try {
//            PrintWriter out = new PrintWriter(address, "UTF-8");
//            out.write(gv.getDotSource());
//            out.close();
//        } catch (FileNotFoundException e2) {
//            e2.printStackTrace();
//        } catch (UnsupportedEncodingException e2) {
//            e2.printStackTrace();
//        }
//    }



}