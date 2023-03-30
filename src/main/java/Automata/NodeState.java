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

public class NodeState implements Comparable<NodeState> {

    private final int state;
    private final int start_index;
    private final int seen_index;

    public NodeState(int state, int start_index, int seen_index) {
        this.state = state;
        this.start_index = start_index;
        this.seen_index = seen_index;
    }

    public int getState() {
        return state;
    }

    public int getStartIndex() {
        return start_index;
    }

    public int getSeenIndex() {
        return seen_index;
    }

    @Override
    public int hashCode() {
        // Randomly chosen prime numbers.
        return state*12553 + start_index*19423 + seen_index*23321;
    }

    @Override
    public boolean equals(Object obj) {
        return (obj instanceof NodeState) &&
               ((NodeState) obj).state == state &&
               ((NodeState) obj).start_index == start_index &&
               ((NodeState) obj).seen_index == seen_index;
    }

    public int compareTo(NodeState obj) {
        if (this.equals(obj)) {
            return 0;
        } else if ((obj.state > state) ||
            (obj.state == state && obj.start_index > start_index) ||
            (obj.state == state && obj.start_index == start_index && obj.seen_index > seen_index)) {
            return -1;
        } else {
            return 1;
        }
    }

    public String toString() {
        return "[" + state + " " + start_index + " " + seen_index + "]";
    }
}
