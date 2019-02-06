package fortress.formats.smt.smtlib;

// Generated from SimpleSExpr.g4 by ANTLR 4.7.2
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link SimpleSExprParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface SimpleSExprVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link SimpleSExprParser#s_exprs}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitS_exprs(SimpleSExprParser.S_exprsContext ctx);
	/**
	 * Visit a parse tree produced by the {@code atom}
	 * labeled alternative in {@link SimpleSExprParser#s_expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAtom(SimpleSExprParser.AtomContext ctx);
	/**
	 * Visit a parse tree produced by the {@code list}
	 * labeled alternative in {@link SimpleSExprParser#s_expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitList(SimpleSExprParser.ListContext ctx);
}
