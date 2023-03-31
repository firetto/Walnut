package Automata;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

class TransducerTest {
    @Test
    void testTransducerRUNSUM2_T() throws Exception {
        // Adapting an integration test to a unit test
        StringBuilder log = new StringBuilder();

        Automaton M =  new Automaton("Word Automata Library/T.txt");
        Assertions.assertEquals(2, M.Q);
        Assertions.assertEquals(
                "[{0=>[0], 1=>[1]}, {0=>[1], 1=>[0]}]",
                M.d.toString());

        Transducer T = new Transducer("Transducer Library/RUNSUM2.txt");
        Automaton C = T.transduceNonDeterministic(M, true, "", log);
        Assertions.assertEquals(
                "[{0=>[0], 1=>[1]}, {0=>[2], 1=>[3]}, {0=>[4], 1=>[5]}, {0=>[6], 1=>[7]}, {0=>[4], 1=>[5]}, {0=>[6], 1=>[7]}, {0=>[0], 1=>[1]}, {0=>[2], 1=>[3]}]",
                C.d.toString());
    }
}
