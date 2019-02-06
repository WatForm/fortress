package fortress.formats.smt.smtlib;

// Generated from SimpleSExpr.g4 by ANTLR 4.7.2
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link SimpleSExprParser}.
 */
public interface SimpleSExprListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link SimpleSExprParser#s_exprs}.
	 * @param ctx the parse tree
	 */
	void enterS_exprs(SimpleSExprParser.S_exprsContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleSExprParser#s_exprs}.
	 * @param ctx the parse tree
	 */
	void exitS_exprs(SimpleSExprParser.S_exprsContext ctx);
	/**
	 * Enter a parse tree produced by the {@code atom}
	 * labeled alternative in {@link SimpleSExprParser#s_expr}.
	 * @param ctx the parse tree
	 */
	void enterAtom(SimpleSExprParser.AtomContext ctx);
	/**
	 * Exit a parse tree produced by the {@code atom}
	 * labeled alternative in {@link SimpleSExprParser#s_expr}.
	 * @param ctx the parse tree
	 */
	void exitAtom(SimpleSExprParser.AtomContext ctx);
	/**
	 * Enter a parse tree produced by the {@code list}
	 * labeled alternative in {@link SimpleSExprParser#s_expr}.
	 * @param ctx the parse tree
	 */
	void enterList(SimpleSExprParser.ListContext ctx);
	/**
	 * Exit a parse tree produced by the {@code list}
	 * labeled alternative in {@link SimpleSExprParser#s_expr}.
	 * @param ctx the parse tree
	 */
	void exitList(SimpleSExprParser.ListContext ctx);
}
