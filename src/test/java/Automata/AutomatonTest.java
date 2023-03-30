package Automata;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

class AutomatonTest {
    @Test
    void testBaseAutomatonConstructor() {
        Automaton a = new Automaton();
        Automaton b = new Automaton();

        try {
            Assertions.assertFalse(a.equals(null));
            //Assertions.assertTrue(a.equals(a));
            //Assertions.assertTrue(a.equals(a.clone()));

        }
        catch (Exception ex) {
            // Hack because everything throws exceptions
            Assertions.fail(ex);
        }


    }

    @Test
    void testBooleanAutomatonConstructor() {
        Automaton a, b;
        try {
            a = new Automaton(true);
            b = new Automaton(true);
            Assertions.assertTrue(a.equals(b));
            Assertions.assertTrue(a.equals(b.clone()));
            b.reverse(false, "", null);
            Assertions.assertTrue(a.equals(b));

            b = new Automaton(false);
            Assertions.assertFalse(a.equals(b));
            Assertions.assertFalse(a.equals(b.clone()));

        }
        catch (Exception ex) {
            // Hack because everything throws exceptions
            Assertions.fail(ex);
        }
    }

    @Test
    void testRegexAutomatonConstructor() {
        Automaton a, b;
        try {
            // regularExpression = "01*" and alphabet = [0,1,2], then the resulting automaton accepts
            //     * words of the form 01* over the alphabet {0,1,2}.<br>
            List<Integer> alphabet = new ArrayList<>();
            alphabet.add(0);
            alphabet.add(1);
            alphabet.add(2);

            a = new Automaton("01*", alphabet);
            Assertions.assertTrue(a.equals(a.clone()));
            List<String> labels = new ArrayList<>();
            labels.add("");
            Assertions.assertEquals(labels.toString(), a.getLabel().toString());

            b = new Automaton("10*", alphabet);
            Assertions.assertFalse(a.equals(b));

            b = a.clone();
            b.reverse(false, "", null);
            Assertions.assertFalse(a.equals(b));
            b.reverse(false, "", null);
            Assertions.assertTrue(a.equals(b));

            b = a.clone();
            b.not(false, "", null);
            Assertions.assertFalse(a.equals(b));
            b.not(false, "", null);
            Assertions.assertTrue(a.equals(b));


        }
        catch (Exception ex) {
            // Hack because everything throws exceptions
            Assertions.fail(ex);
        }
    }

    @Test
    void testAddressAutomatonConstructor() {
        Automaton a, b;
        try {
            a = new Automaton("src/test/resources/LUCAS.txt");
        } catch (Exception ex) {
            // Hack because everything throws exceptions
            Assertions.fail(ex);
        }
    }

}
