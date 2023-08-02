/*   Copyright 2023 Anatoly Zavyalov
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

package Main;

/**
 * The class MutableCounter is a wrapper class for an integer to make it mutable. This is used for tracking the
 * counter for intermediate automata.
 */

public class MutableCounter {
    private int value;
    public MutableCounter() {
        this.value = 0;
    }
    public MutableCounter(int value) {
        this.value = value;
    }
    public void increment() {
        this.value += 1;
    }
    public int getValue() {
        return this.value;
    }
}