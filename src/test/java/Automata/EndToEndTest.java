package Automata;

import Main.Prover;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class EndToEndTest {
    @Test
    void testSimpleFiles() {
        Automaton a, b;
        Prover p;
        String[] args = new String[1];
        args[0] = "src/test/resources/input2.txt";
        try {
            Prover.run(args);
            /*a = new Automaton("src/test/resources/input2.txt");
            a.draw("src/test/tempOutput.gv", "original", true);*/
        } catch (Exception ex) {
            // Hack because everything throws exceptions
            Assertions.fail(ex);
        }
    }

}
