

import java.util.HashMap;

import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import fortress.fol.finite_scope_solver.UIFSolver;

import org.junit.runner.JUnitCore;

import static org.junit.Assert.assertEquals;
import org.junit.Test;
import fortress.fol.*;
import fortress.theory.*;
import fortress.lambda.*;
import fortress.fol.pterm.*;

public class OrBugTest {

  @Test
  public void firstTest() {
      PTerm type = FOL.mkSort("A");
      Var v1 = new Var("v1", type);
      Var v2 = new Var("v2", type);
      Var v3 = new Var("v3", type);
      List<Var> varList = new LinkedList<>();
      varList.add(v1);
      varList.add(v2);
      Term subFormula = FOL.mkAnd(FOL.mkNot(FOL.mkEq(v1, v2)), FOL.mkNot(FOL.mkEq(v3, v2)));
      subFormula = FOL.mkAnd(subFormula, FOL.mkNot(FOL.mkEq(v3, v1)));
      Term exists = FOL.mkExists(varList, subFormula);
      exists = FOL.mkForall(v3, exists);
      Theory result = new Theory("test", Theory.FOL_THEORY);
      result.addAxiom(exists);
      UIFSolver solver = new UIFSolver(result);
      Map<PTerm, Integer> bounds = new HashMap<>();
      bounds.put(type, 2);
      solver.verbosity = 1;
      solver.setUniverseByBounds(bounds);
      assertEquals(solver.checkSat(true, false), false);
  }
}
