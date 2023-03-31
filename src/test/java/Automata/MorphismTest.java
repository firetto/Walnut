package Automata;

import Main.UtilityMethods;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class MorphismTest {
    @Test
    void testGamMorphism() throws Exception {
        Morphism h = new Morphism(UtilityMethods.get_address_for_morphism_library()+"gam.txt");
        Automaton P = h.toWordAutomaton();
        Assertions.assertEquals("[{0=[0], 1=[1]}, {0=[2], 1=[1]}, {0=[0], 1=[3]}, {0=[2], 1=[3]}]", P.d.toString());
    }
}
