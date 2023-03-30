/*   Copyright 2019 Aseem Baranwal
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

import java.util.ArrayList;
import java.util.Collections;
import java.io.File;
import java.util.Iterator;
import java.util.List;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.TreeMap;
import Main.UtilityMethods;

/**
 * The class OstrowskiNumeration includes functionality to produce an adder automaton based on only the<
 * quadratic irrational number alpha that characterizes it. The quadratic irrational is<br>
 * represented using the continued fraction expansion with these two things:<br>
 * - Pre-period, and<br>
 * - Period.<br>
 *
 * For example, for alpha = sqrt(3) - 1, pre-period = [] and period = [1, 2].
 * We only consider alpha < 1, therefore a 0 is always assumed in the preperiod and need not be
 * mentioned in the command.
 */
public class OstrowskiNumeration {
    // The number of states in the 4-input adder is 7.
    static final int NUM_STATES = 7;

    // The value of (r, s) will be in ({-1, 0, 1}, {-2, -1, 0, 1, 2}), so we use 99 to denote none.
    static final int NONE = 99;

    // Name of the number system.
    String name;
    public String getName() { return name; }

    // The pre-period of the continued fraction.
    ArrayList<Integer> preperiod;
    public ArrayList<Integer> getpre_period() { return preperiod; }

    // The pre-period of the continued fraction.
    ArrayList<Integer> period;
    public ArrayList<Integer> get_period() { return period; }

    // The continued fraction expansion of alpha. This is simply a concatenation of
    // preperiod and period.
    ArrayList<Integer> alpha;

    // Size of the list alpha.
    int sz_alpha;

    // Maximum value in the C.F.
    int d_max;

    // Index where the period begins in alpha.
    int period_index;

    // Transitions in the 4-input adder. transition[p][q] = {r, s}.
    // This means state p transitions to state q on input r*d + s, where d is the current digit in
    // the continued fraction expansion of alpha.
    int transition[][][];

    // Maps to keep track of states and transitions.
    TreeMap<NodeState, Integer> index_of_node;
    TreeMap<Integer, NodeState> node_of_index;
    TreeMap<Integer, TreeMap<Integer, List<Integer>>> state_transitions;

    int total_nodes;

    Automaton adder;
    Automaton repr;

    public OstrowskiNumeration(String name, String preperiod, String period) throws Exception {
        this.name = name;
        this.preperiod = new ArrayList<Integer>();
        this.period = new ArrayList<Integer>();
        ParseMethods.parseList(preperiod, this.preperiod);
        ParseMethods.parseList(period, this.period);


        // Remove leading 0's in the preperiod.
        Iterator<Integer> it = this.preperiod.iterator();
        int first_non_zero = 0;
        while (it.hasNext() && it.next() == 0) ++first_non_zero;
        this.preperiod.subList(0, first_non_zero).clear();

        if (this.preperiod.size() == 0) {
            // Easier implementation.
            this.preperiod.addAll(this.period);
        }

        assertValues(this.preperiod);
        assertValues(this.period);

        if (this.preperiod.get(0) == 1) {
            // We want to restrict alpha < 1/2 because otherwise the first two place values in
            // the number system will be 1, which is troublesome.
            if (this.preperiod.size() > 1) {
                this.preperiod.set(0, this.preperiod.get(1) + 1);
                this.preperiod.remove(1);
            } else {
                this.preperiod.set(0, this.period.get(0) + 1);
                this.period.add(this.period.get(0));
                this.period.remove(0);
            }
        }

        this.alpha = new ArrayList<Integer>();
        this.alpha.add(0);
        this.alpha.addAll(this.preperiod);
        this.alpha.addAll(this.period);
        this.period_index = this.preperiod.size() + 1;
        this.sz_alpha = alpha.size();

        d_max = alpha.get(1) - 1;
        for (int i = 2; i < sz_alpha; ++i) {
            d_max = Math.max(alpha.get(i), d_max);
        }

        initTransitions();
        this.index_of_node = new TreeMap<>();
        this.node_of_index = new TreeMap<>();
        this.total_nodes = 0;
    }

    public void createRepresentationAutomaton() throws Exception {
        resetAutomaton();
        repr = new Automaton();

        // Declare the alphabet.
        repr.alphabetSize = d_max + 1;
        List<Integer> list = new ArrayList<Integer>();
        for (int i = 0; i <= d_max; i++) {
            list.add(i);
        }

        // Only 1 input to the repr automaton.
        repr.A.add(list);
        repr.NS.add(null);
        repr.d = new ArrayList<TreeMap<Integer, List<Integer>>>();
        repr.alphabetSize = d_max + 1;
        repr.Q = 0;

        performReprBfs();
        repr.Q = this.total_nodes;
        for(int q = 0; q < this.total_nodes; ++q) {
            if (node_of_index.containsKey(q)) {
                NodeState node = node_of_index.get(q);
                if (node.getState() == 0 && node.getSeenIndex() == 1) {
                    repr.O.add(1);
                } else {
                    repr.O.add(0);
                }
            } else {
                repr.O.add(0);
            }

            this.state_transitions.putIfAbsent(q, new TreeMap<>());
            repr.d.add(this.state_transitions.get(q));
        }

        repr.minimize(false, "", null);
        repr.canonize();

        boolean zeroStateNeeded =
            repr.d.stream().anyMatch(
                tm -> tm.entrySet().stream().anyMatch(
                    es -> es.getValue().get(0) == 0));
        if (!zeroStateNeeded) {
            repr.d.remove(0);
            repr.O.remove(0);
            --repr.Q;
            repr.d.forEach(tm -> {
                tm.forEach((k, v) -> {
                    int dest = v.get(0) - 1;
                    v.set(0, dest);
                });
            });
        }

        String repr_file_name =
            UtilityMethods.get_address_for_custom_bases() + "msd_" + this.name + ".txt";
        File f = new File(repr_file_name);
        if(f.exists() && !f.isDirectory()) {
            throw new Exception("Error: number system " + this.name + " already exists.");
        }
        repr.write(repr_file_name);
        System.out.println("Ostrowski representation automaton created and written to file " + repr_file_name);
    }

    public void createAdderAutomaton() throws Exception {
        resetAutomaton();
        adder = new Automaton();

        // Declare the alphabet.
        adder.alphabetSize = 1;
        List<Integer> list = new ArrayList<Integer>();
        for (int i = 0; i <= d_max; i++) {
            list.add(i);
        }

        // 3 inputs to the adder, all have the same alphabet and the null NumberSystem.
        adder.A.add(list);
        adder.A.add(list);
        adder.A.add(list);
        adder.NS.add(null);
        adder.NS.add(null);
        adder.NS.add(null);
        adder.d = new ArrayList<TreeMap<Integer, List<Integer>>>();
        adder.alphabetSize = (d_max + 1) * (d_max + 1) * (d_max + 1);
        adder.Q = 0;

        performAdderBfs();
        adder.Q = this.total_nodes;
        for(int q = 0; q < this.total_nodes; q++) {
            adder.O.add(isFinal(q)?1:0);
            this.state_transitions.putIfAbsent(q, new TreeMap<>());
            adder.d.add(this.state_transitions.get(q));
        }

        adder.minimize(false, "", null);

        // We need to canonize and remove the first state.
        // The automaton will work with this state as well, but it is useless. This happens
        // because the Automaton class does not support an epsilon transition for NFAs.
        adder.canonize();

        boolean zeroStateNeeded =
            adder.d.stream().anyMatch(
                tm -> tm.entrySet().stream().anyMatch(
                    es -> es.getValue().get(0) == 0));

        if (!zeroStateNeeded) {
            adder.d.remove(0);
            adder.O.remove(0);
            --adder.Q;
            adder.d.forEach(tm -> {
                tm.forEach((k, v) -> {
                    int dest = v.get(0) - 1;
                    // System.out.println(k + " -> " + v);
                    v.set(0, dest);
                });
            });
        }

        // Write the Automaton to file.
        String adder_file_name =
            UtilityMethods.get_address_for_custom_bases() + "msd_" + this.name + "_addition.txt";
        File f = new File(adder_file_name);
        if(f.exists() && !f.isDirectory()) {
            System.out.println("Warning: number system " + this.name + "was previously defined and is being overwritten.");
        }

        adder.write(adder_file_name);
        System.out.println("Ostrowski adder automaton created and written to file " + adder_file_name);
    }

    public String toString() {
        return
            "name: " + this.name +
            ", alpha: " + this.alpha +
            ", period index: " + this.period_index;
    }

    private void assertValues(List<Integer> list) throws Exception {
        if (list == null || list.size() == 0) {
            throw new Exception("The period cannot be empty.");
        }
        Iterator<Integer> it = list.iterator();
        while (it.hasNext()) {
            int d = it.next();
            if (d <= 0) {
                throw new Exception(
                    "Error: All digits of the continued fraction must be positive integers.");
            }
        }
    }

    private int alphaI(int i) {
        if (i < sz_alpha) {
            return alpha.get(i);
        } else {
            return alpha.get(this.period_index + ((i - sz_alpha) % (sz_alpha - this.period_index)));
        }
    }

    private void initTransitions() {
        transition = new int[NUM_STATES][NUM_STATES][2];
        for (int i = 0; i < NUM_STATES; i++) {
            for (int j = 0; j < NUM_STATES; j++) {
                transition[i][j][0] = NONE;
                transition[i][j][1] = NONE;
            }
        }

        transition[0][0][0] = 0;
        transition[0][0][1] = 0;
        transition[0][1][0] = 0;
        transition[0][1][1] = 1;

        transition[1][2][0] = -1;
        transition[1][2][1] = 0;
        transition[1][3][0] = -1;
        transition[1][3][1] = 1;
        transition[1][4][0] = -1;
        transition[1][4][1] = -1;

        transition[2][0][0] = 0;
        transition[2][0][1] = -1;
        transition[2][1][0] = 0;
        transition[2][1][1] = 0;

        transition[3][2][0] = -1;
        transition[3][2][1] = -1;
        transition[3][3][0] = -1;
        transition[3][3][1] = 0;
        transition[3][4][0] = -1;
        transition[3][4][1] = -2;

        transition[4][5][0] = 1;
        transition[4][5][1] = 0;
        transition[4][6][0] = 1;
        transition[4][6][1] = -1;

        transition[5][2][0] = -1;
        transition[5][2][1] = 1;
        transition[5][3][0] = -1;
        transition[5][3][1] = 2;
        transition[5][4][0] = -1;
        transition[5][4][1] = 0;

        transition[6][0][0] = 0;
        transition[6][0][1] = 1;
        transition[6][1][0] = 0;
        transition[6][1][1] = 2;
    }

    private void performAdderBfs() {
        // In a node, the indices mean the following.
        // 0: The state in the 4-input automaton.
        // 1: The C.F. index at which the input started.
        // 2: The C.F. index that is currently active in the input.

        // This is the start state.
        NodeState start_node = new NodeState(0, 0, 0);
        this.index_of_node.put(start_node, 0);
        this.node_of_index.put(0, start_node);
        ++this.total_nodes;

        Queue<Integer> queue = new LinkedList<Integer>();
        this.state_transitions = new TreeMap<>();

        // These are the "0" states.
        this.state_transitions.put(0, new TreeMap<>());
        for (int i = 1; i < this.sz_alpha; i++) {
            NodeState node = new NodeState(0, i, i);
            index_of_node.put(node, this.total_nodes);
            node_of_index.put(this.total_nodes, node);
            addTransitions(this.state_transitions.get(0), 0, this.total_nodes);
            queue.add(this.total_nodes);
            ++this.total_nodes;
        }

        int r, s, a;
        while (queue.size() > 0) {
            int cur_node_idx = queue.remove();
            NodeState cur_node = node_of_index.get(cur_node_idx);
            int state = cur_node.getState();
            int start_index = cur_node.getStartIndex();
            int seen_index = cur_node.getSeenIndex();

            if (seen_index == 1 && this.sz_alpha > 2 && this.period_index > 1) {
                // The input ends here.
                continue;
            }

            for (int st = 0; st < NUM_STATES; st++) {
                r = this.transition[state][st][0];
                s = this.transition[state][st][1];

                if (r == NONE || s == NONE) {
                    continue;
                }

                if (seen_index > 1) {
                    NodeState node = new NodeState(st, start_index, seen_index - 1);
                    this.state_transitions.putIfAbsent(cur_node_idx, new TreeMap<>());
                    a = alphaI(seen_index - 1);
                    if (index_of_node.containsKey(node)) {
                        // This node already exists, don't create a new NodeState.
                        addTransitions(
                            this.state_transitions.get(cur_node_idx),
                            a*r + s,
                            index_of_node.get(node));
                    } else {
                        // Need to create a new NodeState.
                        index_of_node.put(node, this.total_nodes);
                        node_of_index.put(this.total_nodes, node);
                        queue.add(this.total_nodes);
                        addTransitions(
                            this.state_transitions.get(cur_node_idx),
                            a*r + s,
                            this.total_nodes);
                        ++this.total_nodes;
                    }
                }

                if (seen_index == this.period_index) {
                    // There is another possibility.
                    // Next index could also be sz_alpha - 1.
                    NodeState node = new NodeState(st, start_index, sz_alpha - 1);

                    // Create the map if does not exist.
                    this.state_transitions.putIfAbsent(cur_node_idx, new TreeMap<>());

                    a = alphaI(sz_alpha - 1);
                    if (index_of_node.containsKey(node)) {
                        addTransitions(
                            this.state_transitions.get(cur_node_idx),
                            a*r + s,
                            index_of_node.get(node));
                    } else {
                        index_of_node.put(node, this.total_nodes);
                        node_of_index.put(this.total_nodes, node);
                        queue.add(this.total_nodes);
                        addTransitions(
                            this.state_transitions.get(cur_node_idx),
                            a*r + s,
                            this.total_nodes);
                        ++this.total_nodes;
                    }
                }
            }
        }
    }

    private void performReprBfs() {
        // In a node, the indices mean the following.
        // 0: The state in the 2-input automaton.
        // 1: The C.F. index at which the input started.
        // 2: The C.F. index that is currently active in the input.

        // This is the start state.
        NodeState start_node = new NodeState(0, 0, 0);
        this.index_of_node.put(start_node, 0);
        this.node_of_index.put(0, start_node);
        ++this.total_nodes;

        Queue<Integer> queue = new LinkedList<Integer>();
        this.state_transitions = new TreeMap<>();
        int a;

        // These are the "0" states.
        this.state_transitions.put(0, new TreeMap<>());
        for (int i = 1; i < this.sz_alpha; ++i) {
            NodeState node = new NodeState(0, i, i);
            a = alphaI(i);
            index_of_node.put(node, this.total_nodes);
            node_of_index.put(this.total_nodes, node);
            for (int inp = 0; inp < a; ++inp) {
                this.state_transitions.get(0).putIfAbsent(inp, new ArrayList<Integer>());
                this.state_transitions.get(0).get(inp).add(this.total_nodes);
            }

            queue.add(this.total_nodes);
            ++this.total_nodes;

            node = new NodeState(1, i, i);
            index_of_node.put(node, this.total_nodes);
            node_of_index.put(this.total_nodes, node);
            this.state_transitions.get(0).putIfAbsent(a, new ArrayList<Integer>());
            this.state_transitions.get(0).get(a).add(this.total_nodes);
            queue.add(this.total_nodes);
            ++this.total_nodes;
        }

        while (queue.size() > 0) {
            int cur_node_idx = queue.remove();

            NodeState cur_node = node_of_index.get(cur_node_idx);
            int state = cur_node.getState();
            int start_index = cur_node.getStartIndex();
            int seen_index = cur_node.getSeenIndex();

            if (seen_index == 1 && this.sz_alpha > 2 && this.period_index > 1) {
                // The input ends here.
                continue;
            }

            if (seen_index > 1) {
                a = alphaI(seen_index - 1);
                if (state == 1) {
                    // Can only take a "0" transition from a "1" state.
                    a = 1;
                }

                this.state_transitions.putIfAbsent(cur_node_idx, new TreeMap<>());

                // Will go to state 0 for all transitions < a.
                NodeState node = new NodeState(0, start_index, seen_index - 1);
                for (int inp = 0; inp < a; ++inp) {
                    if (index_of_node.containsKey(node)) {
                        this.state_transitions
                            .get(cur_node_idx)
                            .putIfAbsent(inp, new ArrayList<Integer>());
                        this.state_transitions
                            .get(cur_node_idx)
                            .get(inp)
                            .add(index_of_node.get(node));
                    } else {
                        index_of_node.put(node, this.total_nodes);
                        node_of_index.put(this.total_nodes, node);
                        queue.add(this.total_nodes);
                        this.state_transitions
                            .get(cur_node_idx)
                            .putIfAbsent(inp, new ArrayList<Integer>());
                        this.state_transitions
                            .get(cur_node_idx)
                            .get(inp)
                            .add(this.total_nodes);
                        ++this.total_nodes;
                    }
                }

                // Go to state 1 from this state 0 for transition = a (only if seen_index > 2).
                if (state == 0 && seen_index > 2) {
                    node = new NodeState(1, start_index, seen_index - 1);
                    if (index_of_node.containsKey(node)) {
                        this.state_transitions
                            .get(cur_node_idx)
                            .putIfAbsent(a, new ArrayList<Integer>());
                        this.state_transitions
                            .get(cur_node_idx)
                            .get(a)
                            .add(index_of_node.get(node));
                    } else {
                        index_of_node.put(node, this.total_nodes);
                        node_of_index.put(this.total_nodes, node);
                        queue.add(this.total_nodes);
                        this.state_transitions
                            .get(cur_node_idx)
                            .putIfAbsent(a, new ArrayList<Integer>());
                        this.state_transitions
                            .get(cur_node_idx)
                            .get(a)
                            .add(this.total_nodes);
                        ++this.total_nodes;
                    }
                }
            }

            if (seen_index == this.period_index) {
                // There is another possibility.
                // Next index could also be sz_alpha - 1.
                a = alphaI(sz_alpha - 1);
                if (state == 1) {
                    // Can only take a "0" transition from a "1" state.
                    a = 1;
                }

                // Create the map if does not exist.
                this.state_transitions.putIfAbsent(cur_node_idx, new TreeMap<>());
                NodeState node = new NodeState(0, start_index, sz_alpha - 1);
                for (int inp = 0; inp < a; ++inp) {
                    if (index_of_node.containsKey(node)) {
                        this.state_transitions
                            .get(cur_node_idx)
                            .putIfAbsent(inp, new ArrayList<Integer>());
                        this.state_transitions
                            .get(cur_node_idx)
                            .get(inp)
                            .add(index_of_node.get(node));
                    } else {
                        index_of_node.put(node, this.total_nodes);
                        node_of_index.put(this.total_nodes, node);
                        queue.add(this.total_nodes);
                        this.state_transitions
                            .get(cur_node_idx)
                            .putIfAbsent(inp, new ArrayList<Integer>());
                        this.state_transitions
                            .get(cur_node_idx)
                            .get(inp)
                            .add(this.total_nodes);
                        ++this.total_nodes;
                    }
                }

                // Go to state 1 from this state 0 for transition = a.
                if (state == 0) {
                    node = new NodeState(1, start_index, sz_alpha - 1);
                    if (index_of_node.containsKey(node)) {
                        this.state_transitions
                            .get(cur_node_idx)
                            .putIfAbsent(a, new ArrayList<Integer>());
                        this.state_transitions
                            .get(cur_node_idx)
                            .get(a)
                            .add(index_of_node.get(node));
                    } else {
                        index_of_node.put(node, this.total_nodes);
                        node_of_index.put(this.total_nodes, node);
                        queue.add(this.total_nodes);
                        this.state_transitions
                            .get(cur_node_idx)
                            .putIfAbsent(a, new ArrayList<Integer>());
                        this.state_transitions
                            .get(cur_node_idx)
                            .get(a)
                            .add(this.total_nodes);
                        ++this.total_nodes;
                    }
                }
            }
        }
    }

    private void addTransitions(
        TreeMap<Integer, List<Integer>> current_state_transitions,
        int diff,
        int encodedDestination) {
        for (int x = 0; x <= d_max; ++x) {
            for (int y = 0; y <= d_max; ++y) {
                for (int z = 0; z <= d_max; ++z) {
                    if (z - x - y == diff) {
                        int input = inputEncode(x, y, z);
                        current_state_transitions.putIfAbsent(input, new ArrayList<Integer>());
                        current_state_transitions.get(input).add(encodedDestination);
                    }
                }
            }
        }
    }

    private int inputEncode(int x, int y, int z) {
        return x + (d_max+1)*y + (d_max+1)*(d_max+1)*z;
    }

    private boolean isFinal(int node_index) {
        NodeState node = node_of_index.get(node_index);
        return (
            // (node.getState() + node.getStartIndex() + node.getSeenIndex() == 0) ||
            ((node.getState() == 0 || node.getState() == 2 || node.getState() == 6) &&
                node.getSeenIndex() == 1));
    }

    private void resetAutomaton() {
        this.index_of_node = new TreeMap<>();
        this.node_of_index = new TreeMap<>();
        this.state_transitions = new TreeMap<>();
        this.total_nodes = 0;
    }
}
