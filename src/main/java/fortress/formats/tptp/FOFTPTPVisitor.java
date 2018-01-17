// Generated from FOFTPTP.g4 by ANTLR 4.5.2
package fortress.formats.tptp;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link FOFTPTPParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface FOFTPTPVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link FOFTPTPParser#spec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSpec(FOFTPTPParser.SpecContext ctx);
	/**
	 * Visit a parse tree produced by {@link FOFTPTPParser#fof_annotated}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFof_annotated(FOFTPTPParser.Fof_annotatedContext ctx);
	/**
	 * Visit a parse tree produced by the {@code not}
	 * labeled alternative in {@link FOFTPTPParser#fof_formula}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNot(FOFTPTPParser.NotContext ctx);
	/**
	 * Visit a parse tree produced by the {@code paren}
	 * labeled alternative in {@link FOFTPTPParser#fof_formula}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitParen(FOFTPTPParser.ParenContext ctx);
	/**
	 * Visit a parse tree produced by the {@code or}
	 * labeled alternative in {@link FOFTPTPParser#fof_formula}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitOr(FOFTPTPParser.OrContext ctx);
	/**
	 * Visit a parse tree produced by the {@code pred}
	 * labeled alternative in {@link FOFTPTPParser#fof_formula}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPred(FOFTPTPParser.PredContext ctx);
	/**
	 * Visit a parse tree produced by the {@code and}
	 * labeled alternative in {@link FOFTPTPParser#fof_formula}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAnd(FOFTPTPParser.AndContext ctx);
	/**
	 * Visit a parse tree produced by the {@code forall}
	 * labeled alternative in {@link FOFTPTPParser#fof_formula}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitForall(FOFTPTPParser.ForallContext ctx);
	/**
	 * Visit a parse tree produced by the {@code prop}
	 * labeled alternative in {@link FOFTPTPParser#fof_formula}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProp(FOFTPTPParser.PropContext ctx);
	/**
	 * Visit a parse tree produced by the {@code iff}
	 * labeled alternative in {@link FOFTPTPParser#fof_formula}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIff(FOFTPTPParser.IffContext ctx);
	/**
	 * Visit a parse tree produced by the {@code exists}
	 * labeled alternative in {@link FOFTPTPParser#fof_formula}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExists(FOFTPTPParser.ExistsContext ctx);
	/**
	 * Visit a parse tree produced by the {@code neq}
	 * labeled alternative in {@link FOFTPTPParser#fof_formula}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNeq(FOFTPTPParser.NeqContext ctx);
	/**
	 * Visit a parse tree produced by the {@code eq}
	 * labeled alternative in {@link FOFTPTPParser#fof_formula}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitEq(FOFTPTPParser.EqContext ctx);
	/**
	 * Visit a parse tree produced by the {@code imp}
	 * labeled alternative in {@link FOFTPTPParser#fof_formula}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitImp(FOFTPTPParser.ImpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code conVar}
	 * labeled alternative in {@link FOFTPTPParser#term}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitConVar(FOFTPTPParser.ConVarContext ctx);
	/**
	 * Visit a parse tree produced by the {@code apply}
	 * labeled alternative in {@link FOFTPTPParser#term}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitApply(FOFTPTPParser.ApplyContext ctx);
}