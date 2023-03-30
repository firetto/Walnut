/*   Copyright 2021 Laindon Burnett
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

import Main.UtilityMethods;

import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.HashSet;
import java.util.List;
import java.util.Collections;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.TreeMap;

/**
 * The class Morphism represents a morphism from a finite alphabet to the integers, 
 * defined by the integer word it sends each member of the alphabet to.
 *
 * For example, with an alphabet of {0, 1, 2}, we define the mappings 
 * 0 -> [-3]0102[11],
 * 1 -> 2113,
 * 2 -> 314
 * 
 * Here square brackets are used to specify a number not in the range 0-9
 */
public class Morphism {
    // The name of the morphism
    public String name;

    // The uniform length of the image of a letter, when applicable
    public Integer length;

    // The mapping between each letter of the alphabet and its image under the morphism
    public TreeMap<Integer, List<Integer>> mapping;

    // The set of values in the image of the morphism
    public HashSet<Integer> range;

    // The syntax for declaring a morphism in the command line is identical to that
    // of a saved morphism file, so we reuse this constructor
    public Morphism(String name, String mapString) throws Exception {
        this.name = name;
        this.mapping = ParseMethods.parseMorphism(mapString);
        this.range = new HashSet<Integer>();
        for (Integer key : mapping.keySet()) {
            for (Integer number : mapping.get(key)) {
                range.add(number);
            }
        }
    }

    // Reads the entirety of a file and passes this into the more general constructor
    public Morphism(String address) throws Exception {
        this("", new String(Files.readAllBytes(Paths.get(address)), StandardCharsets.UTF_8));
    }

    public void write(String address) throws Exception {
        PrintWriter out = new PrintWriter(address, "UTF-8");
        for (Integer x : mapping.keySet()) {
            out.write(x.toString()+" -> ");
            for (Integer y : mapping.get(x)) {
                if ((0 <= y) && (9 >= y)) {
                    out.write(y.toString());
                }
                else {
                    out.write("["+y.toString()+"]");
                }
            }
            out.write(UtilityMethods.newLine());
        }
        out.close();
    }

    public Automaton toWordAutomaton() throws Exception {
        Integer maxImageLength = 0;
        for (int x : mapping.keySet()) {
            int length = mapping.get(x).size();
            if (length > maxImageLength) {
                maxImageLength = length;
            }
        }
        Automaton promotion = new Automaton();
        List<Integer> alphabet = IntStream.rangeClosed(0, maxImageLength-1).boxed().collect(Collectors.toList());
        promotion.A.add(alphabet);
        int maxEntry = 0;
        for (int x : mapping.keySet()) {
            for (int y : mapping.get(x)) {
                if (y < 0) {
                    throw new Exception("Cannot promote a morphism with negative values.");
                }
                else if (y > maxEntry) {
                    maxEntry = y;
                }
            }
        }
        promotion.Q = maxEntry+1;
        promotion.O = IntStream.rangeClosed(0, promotion.Q-1).boxed().collect(Collectors.toList());
        for (int x : mapping.keySet()) {
            TreeMap<Integer, List<Integer>> xmap = new TreeMap<Integer, List<Integer>>();
            for (int i=0; i<mapping.get(x).size(); i++) {
                xmap.put(i, Collections.singletonList(mapping.get(x).get(i)));
            }
            promotion.d.add(xmap);
        }
        // this word automaton is purely symbolic in input and we want it in the exact order given
        promotion.canonized = true;
        // the base for the automata is the length of the longest image of any letter under the morphism
        promotion.NS.add(new NumberSystem("msd_" + maxImageLength.toString()));

        return promotion;
    }

    // Determines whether the morphism is uniform, meaning whether or not the image of every input symbol in the alphabet
    // has the same length.
    public boolean isUniform() {
        boolean firstElement = true;
        int imageLength = 0;
        for (int x : mapping.keySet()) {
            if (firstElement) {
                imageLength = mapping.get(x).size();
                firstElement = false;
            }
            else if (mapping.get(x).size() != imageLength) {
                return false;
            }
        }
        this.length = imageLength;
        return true;
    }

    // Generates a command to define an intermediary word automaton given an integer i that accepts iff an i appears in position n of a word
    // These can then be combined efficiently with a combine command as they have disjoint domains
    public String makeInterCommand(Integer i, String baseAutomatonName, String numSys) {
        if (numSys != "") {
            numSys = "?" + numSys;
        }
        String interCommand = "def " + baseAutomatonName + "_" + i.toString();
		interCommand += " \"" + numSys + " E q, r (n=" + length.toString() + "*q+r & r>=0 & r<" + length.toString();
		for (Integer key : this.mapping.keySet()) {
			boolean exists = false;
			String clause = " & (" + baseAutomatonName + "[q]";
            List<Integer> symbolImage = this.mapping.get(key);
			for (Integer j=0; j<symbolImage.size(); j++) {
    			if (symbolImage.get(j) == i) {
					if(! exists) {
						clause += "= @" + key.toString() + " => (r=" + j.toString();
						exists = true;
					}
					else {
						clause += "|r=" + j.toString();
					}
				}
			}
			if (exists) {
				clause += "))";
			}
			else {
				clause += "!= @" + key.toString() + ")";
			}
			interCommand += clause;
		}
		interCommand += ")\":";
        return interCommand;
    }



}
