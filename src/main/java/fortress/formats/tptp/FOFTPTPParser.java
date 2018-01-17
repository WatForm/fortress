// Generated from FOFTPTP.g4 by ANTLR 4.5.2
package fortress.formats.tptp;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class FOFTPTPParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.5.2", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__0=1, T__1=2, T__2=3, T__3=4, T__4=5, T__5=6, T__6=7, T__7=8, T__8=9, 
		T__9=10, T__10=11, T__11=12, T__12=13, T__13=14, T__14=15, T__15=16, T__16=17, 
		ID=18, WS=19, COMMENT=20;
	public static final int
		RULE_spec = 0, RULE_fof_annotated = 1, RULE_fof_formula = 2, RULE_term = 3;
	public static final String[] ruleNames = {
		"spec", "fof_annotated", "fof_formula", "term"
	};

	private static final String[] _LITERAL_NAMES = {
		null, "'fof'", "'('", "','", "')'", "'.'", "'~'", "'!'", "'['", "']'", 
		"':'", "'?'", "'&'", "'|'", "'=>'", "'<=>'", "'='", "'!='"
	};
	private static final String[] _SYMBOLIC_NAMES = {
		null, null, null, null, null, null, null, null, null, null, null, null, 
		null, null, null, null, null, null, "ID", "WS", "COMMENT"
	};
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}

	@Override
	public String getGrammarFileName() { return "FOFTPTP.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public FOFTPTPParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}
	public static class SpecContext extends ParserRuleContext {
		public List<Fof_annotatedContext> fof_annotated() {
			return getRuleContexts(Fof_annotatedContext.class);
		}
		public Fof_annotatedContext fof_annotated(int i) {
			return getRuleContext(Fof_annotatedContext.class,i);
		}
		public SpecContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_spec; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof FOFTPTPVisitor ) return ((FOFTPTPVisitor<? extends T>)visitor).visitSpec(this);
			else return visitor.visitChildren(this);
		}
	}

	public final SpecContext spec() throws RecognitionException {
		SpecContext _localctx = new SpecContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_spec);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(9); 
			_errHandler.sync(this);
			_la = _input.LA(1);
			do {
				{
				{
				setState(8);
				fof_annotated();
				}
				}
				setState(11); 
				_errHandler.sync(this);
				_la = _input.LA(1);
			} while ( _la==T__0 );
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Fof_annotatedContext extends ParserRuleContext {
		public List<TerminalNode> ID() { return getTokens(FOFTPTPParser.ID); }
		public TerminalNode ID(int i) {
			return getToken(FOFTPTPParser.ID, i);
		}
		public Fof_formulaContext fof_formula() {
			return getRuleContext(Fof_formulaContext.class,0);
		}
		public Fof_annotatedContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_fof_annotated; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof FOFTPTPVisitor ) return ((FOFTPTPVisitor<? extends T>)visitor).visitFof_annotated(this);
			else return visitor.visitChildren(this);
		}
	}

	public final Fof_annotatedContext fof_annotated() throws RecognitionException {
		Fof_annotatedContext _localctx = new Fof_annotatedContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_fof_annotated);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(13);
			match(T__0);
			setState(14);
			match(T__1);
			setState(15);
			match(ID);
			setState(16);
			match(T__2);
			setState(17);
			match(ID);
			setState(18);
			match(T__2);
			setState(19);
			fof_formula(0);
			setState(20);
			match(T__3);
			setState(21);
			match(T__4);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Fof_formulaContext extends ParserRuleContext {
		public Fof_formulaContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_fof_formula; }
	 
		public Fof_formulaContext() { }
		public void copyFrom(Fof_formulaContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class NotContext extends Fof_formulaContext {
		public Fof_formulaContext fof_formula() {
			return getRuleContext(Fof_formulaContext.class,0);
		}
		public NotContext(Fof_formulaContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof FOFTPTPVisitor ) return ((FOFTPTPVisitor<? extends T>)visitor).visitNot(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class ParenContext extends Fof_formulaContext {
		public Fof_formulaContext fof_formula() {
			return getRuleContext(Fof_formulaContext.class,0);
		}
		public ParenContext(Fof_formulaContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof FOFTPTPVisitor ) return ((FOFTPTPVisitor<? extends T>)visitor).visitParen(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class OrContext extends Fof_formulaContext {
		public List<Fof_formulaContext> fof_formula() {
			return getRuleContexts(Fof_formulaContext.class);
		}
		public Fof_formulaContext fof_formula(int i) {
			return getRuleContext(Fof_formulaContext.class,i);
		}
		public OrContext(Fof_formulaContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof FOFTPTPVisitor ) return ((FOFTPTPVisitor<? extends T>)visitor).visitOr(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class PredContext extends Fof_formulaContext {
		public TerminalNode ID() { return getToken(FOFTPTPParser.ID, 0); }
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public PredContext(Fof_formulaContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof FOFTPTPVisitor ) return ((FOFTPTPVisitor<? extends T>)visitor).visitPred(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class AndContext extends Fof_formulaContext {
		public List<Fof_formulaContext> fof_formula() {
			return getRuleContexts(Fof_formulaContext.class);
		}
		public Fof_formulaContext fof_formula(int i) {
			return getRuleContext(Fof_formulaContext.class,i);
		}
		public AndContext(Fof_formulaContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof FOFTPTPVisitor ) return ((FOFTPTPVisitor<? extends T>)visitor).visitAnd(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class ForallContext extends Fof_formulaContext {
		public List<TerminalNode> ID() { return getTokens(FOFTPTPParser.ID); }
		public TerminalNode ID(int i) {
			return getToken(FOFTPTPParser.ID, i);
		}
		public Fof_formulaContext fof_formula() {
			return getRuleContext(Fof_formulaContext.class,0);
		}
		public ForallContext(Fof_formulaContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof FOFTPTPVisitor ) return ((FOFTPTPVisitor<? extends T>)visitor).visitForall(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class PropContext extends Fof_formulaContext {
		public TerminalNode ID() { return getToken(FOFTPTPParser.ID, 0); }
		public PropContext(Fof_formulaContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof FOFTPTPVisitor ) return ((FOFTPTPVisitor<? extends T>)visitor).visitProp(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class IffContext extends Fof_formulaContext {
		public List<Fof_formulaContext> fof_formula() {
			return getRuleContexts(Fof_formulaContext.class);
		}
		public Fof_formulaContext fof_formula(int i) {
			return getRuleContext(Fof_formulaContext.class,i);
		}
		public IffContext(Fof_formulaContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof FOFTPTPVisitor ) return ((FOFTPTPVisitor<? extends T>)visitor).visitIff(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class ExistsContext extends Fof_formulaContext {
		public List<TerminalNode> ID() { return getTokens(FOFTPTPParser.ID); }
		public TerminalNode ID(int i) {
			return getToken(FOFTPTPParser.ID, i);
		}
		public Fof_formulaContext fof_formula() {
			return getRuleContext(Fof_formulaContext.class,0);
		}
		public ExistsContext(Fof_formulaContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof FOFTPTPVisitor ) return ((FOFTPTPVisitor<? extends T>)visitor).visitExists(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class NeqContext extends Fof_formulaContext {
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public NeqContext(Fof_formulaContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof FOFTPTPVisitor ) return ((FOFTPTPVisitor<? extends T>)visitor).visitNeq(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class EqContext extends Fof_formulaContext {
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public EqContext(Fof_formulaContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof FOFTPTPVisitor ) return ((FOFTPTPVisitor<? extends T>)visitor).visitEq(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class ImpContext extends Fof_formulaContext {
		public List<Fof_formulaContext> fof_formula() {
			return getRuleContexts(Fof_formulaContext.class);
		}
		public Fof_formulaContext fof_formula(int i) {
			return getRuleContext(Fof_formulaContext.class,i);
		}
		public ImpContext(Fof_formulaContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof FOFTPTPVisitor ) return ((FOFTPTPVisitor<? extends T>)visitor).visitImp(this);
			else return visitor.visitChildren(this);
		}
	}

	public final Fof_formulaContext fof_formula() throws RecognitionException {
		return fof_formula(0);
	}

	private Fof_formulaContext fof_formula(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		Fof_formulaContext _localctx = new Fof_formulaContext(_ctx, _parentState);
		Fof_formulaContext _prevctx = _localctx;
		int _startState = 4;
		enterRecursionRule(_localctx, 4, RULE_fof_formula, _p);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(77);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,4,_ctx) ) {
			case 1:
				{
				_localctx = new NotContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;

				setState(24);
				match(T__5);
				setState(25);
				fof_formula(12);
				}
				break;
			case 2:
				{
				_localctx = new ForallContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(26);
				match(T__6);
				setState(27);
				match(T__7);
				setState(28);
				match(ID);
				setState(33);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__2) {
					{
					{
					setState(29);
					match(T__2);
					setState(30);
					match(ID);
					}
					}
					setState(35);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(36);
				match(T__8);
				setState(37);
				match(T__9);
				setState(38);
				fof_formula(11);
				}
				break;
			case 3:
				{
				_localctx = new ExistsContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(39);
				match(T__10);
				setState(40);
				match(T__7);
				setState(41);
				match(ID);
				setState(46);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__2) {
					{
					{
					setState(42);
					match(T__2);
					setState(43);
					match(ID);
					}
					}
					setState(48);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(49);
				match(T__8);
				setState(50);
				match(T__9);
				setState(51);
				fof_formula(10);
				}
				break;
			case 4:
				{
				_localctx = new EqContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(52);
				term();
				setState(53);
				match(T__15);
				setState(54);
				term();
				}
				break;
			case 5:
				{
				_localctx = new NeqContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(56);
				term();
				setState(57);
				match(T__16);
				setState(58);
				term();
				}
				break;
			case 6:
				{
				_localctx = new PropContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(60);
				match(ID);
				}
				break;
			case 7:
				{
				_localctx = new PredContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(61);
				match(ID);
				setState(62);
				match(T__1);
				setState(63);
				term();
				setState(68);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__2) {
					{
					{
					setState(64);
					match(T__2);
					setState(65);
					term();
					}
					}
					setState(70);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(71);
				match(T__3);
				}
				break;
			case 8:
				{
				_localctx = new ParenContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(73);
				match(T__1);
				setState(74);
				fof_formula(0);
				setState(75);
				match(T__3);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(93);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,6,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(91);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,5,_ctx) ) {
					case 1:
						{
						_localctx = new AndContext(new Fof_formulaContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_fof_formula);
						setState(79);
						if (!(precpred(_ctx, 9))) throw new FailedPredicateException(this, "precpred(_ctx, 9)");
						setState(80);
						match(T__11);
						setState(81);
						fof_formula(10);
						}
						break;
					case 2:
						{
						_localctx = new OrContext(new Fof_formulaContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_fof_formula);
						setState(82);
						if (!(precpred(_ctx, 8))) throw new FailedPredicateException(this, "precpred(_ctx, 8)");
						setState(83);
						match(T__12);
						setState(84);
						fof_formula(9);
						}
						break;
					case 3:
						{
						_localctx = new ImpContext(new Fof_formulaContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_fof_formula);
						setState(85);
						if (!(precpred(_ctx, 7))) throw new FailedPredicateException(this, "precpred(_ctx, 7)");
						setState(86);
						match(T__13);
						setState(87);
						fof_formula(8);
						}
						break;
					case 4:
						{
						_localctx = new IffContext(new Fof_formulaContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_fof_formula);
						setState(88);
						if (!(precpred(_ctx, 6))) throw new FailedPredicateException(this, "precpred(_ctx, 6)");
						setState(89);
						match(T__14);
						setState(90);
						fof_formula(7);
						}
						break;
					}
					} 
				}
				setState(95);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,6,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class TermContext extends ParserRuleContext {
		public TermContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_term; }
	 
		public TermContext() { }
		public void copyFrom(TermContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class ApplyContext extends TermContext {
		public TerminalNode ID() { return getToken(FOFTPTPParser.ID, 0); }
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public ApplyContext(TermContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof FOFTPTPVisitor ) return ((FOFTPTPVisitor<? extends T>)visitor).visitApply(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class ConVarContext extends TermContext {
		public TerminalNode ID() { return getToken(FOFTPTPParser.ID, 0); }
		public ConVarContext(TermContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof FOFTPTPVisitor ) return ((FOFTPTPVisitor<? extends T>)visitor).visitConVar(this);
			else return visitor.visitChildren(this);
		}
	}

	public final TermContext term() throws RecognitionException {
		TermContext _localctx = new TermContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_term);
		int _la;
		try {
			setState(109);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,8,_ctx) ) {
			case 1:
				_localctx = new ConVarContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(96);
				match(ID);
				}
				break;
			case 2:
				_localctx = new ApplyContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(97);
				match(ID);
				setState(98);
				match(T__1);
				setState(99);
				term();
				setState(104);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__2) {
					{
					{
					setState(100);
					match(T__2);
					setState(101);
					term();
					}
					}
					setState(106);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(107);
				match(T__3);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public boolean sempred(RuleContext _localctx, int ruleIndex, int predIndex) {
		switch (ruleIndex) {
		case 2:
			return fof_formula_sempred((Fof_formulaContext)_localctx, predIndex);
		}
		return true;
	}
	private boolean fof_formula_sempred(Fof_formulaContext _localctx, int predIndex) {
		switch (predIndex) {
		case 0:
			return precpred(_ctx, 9);
		case 1:
			return precpred(_ctx, 8);
		case 2:
			return precpred(_ctx, 7);
		case 3:
			return precpred(_ctx, 6);
		}
		return true;
	}

	public static final String _serializedATN =
		"\3\u0430\ud6d1\u8206\uad2d\u4417\uaef1\u8d80\uaadd\3\26r\4\2\t\2\4\3\t"+
		"\3\4\4\t\4\4\5\t\5\3\2\6\2\f\n\2\r\2\16\2\r\3\3\3\3\3\3\3\3\3\3\3\3\3"+
		"\3\3\3\3\3\3\3\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\7\4\"\n\4\f\4\16\4%\13"+
		"\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\7\4/\n\4\f\4\16\4\62\13\4\3\4\3\4\3"+
		"\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\7\4E\n\4\f"+
		"\4\16\4H\13\4\3\4\3\4\3\4\3\4\3\4\3\4\5\4P\n\4\3\4\3\4\3\4\3\4\3\4\3\4"+
		"\3\4\3\4\3\4\3\4\3\4\3\4\7\4^\n\4\f\4\16\4a\13\4\3\5\3\5\3\5\3\5\3\5\3"+
		"\5\7\5i\n\5\f\5\16\5l\13\5\3\5\3\5\5\5p\n\5\3\5\2\3\6\6\2\4\6\b\2\2~\2"+
		"\13\3\2\2\2\4\17\3\2\2\2\6O\3\2\2\2\bo\3\2\2\2\n\f\5\4\3\2\13\n\3\2\2"+
		"\2\f\r\3\2\2\2\r\13\3\2\2\2\r\16\3\2\2\2\16\3\3\2\2\2\17\20\7\3\2\2\20"+
		"\21\7\4\2\2\21\22\7\24\2\2\22\23\7\5\2\2\23\24\7\24\2\2\24\25\7\5\2\2"+
		"\25\26\5\6\4\2\26\27\7\6\2\2\27\30\7\7\2\2\30\5\3\2\2\2\31\32\b\4\1\2"+
		"\32\33\7\b\2\2\33P\5\6\4\16\34\35\7\t\2\2\35\36\7\n\2\2\36#\7\24\2\2\37"+
		" \7\5\2\2 \"\7\24\2\2!\37\3\2\2\2\"%\3\2\2\2#!\3\2\2\2#$\3\2\2\2$&\3\2"+
		"\2\2%#\3\2\2\2&\'\7\13\2\2\'(\7\f\2\2(P\5\6\4\r)*\7\r\2\2*+\7\n\2\2+\60"+
		"\7\24\2\2,-\7\5\2\2-/\7\24\2\2.,\3\2\2\2/\62\3\2\2\2\60.\3\2\2\2\60\61"+
		"\3\2\2\2\61\63\3\2\2\2\62\60\3\2\2\2\63\64\7\13\2\2\64\65\7\f\2\2\65P"+
		"\5\6\4\f\66\67\5\b\5\2\678\7\22\2\289\5\b\5\29P\3\2\2\2:;\5\b\5\2;<\7"+
		"\23\2\2<=\5\b\5\2=P\3\2\2\2>P\7\24\2\2?@\7\24\2\2@A\7\4\2\2AF\5\b\5\2"+
		"BC\7\5\2\2CE\5\b\5\2DB\3\2\2\2EH\3\2\2\2FD\3\2\2\2FG\3\2\2\2GI\3\2\2\2"+
		"HF\3\2\2\2IJ\7\6\2\2JP\3\2\2\2KL\7\4\2\2LM\5\6\4\2MN\7\6\2\2NP\3\2\2\2"+
		"O\31\3\2\2\2O\34\3\2\2\2O)\3\2\2\2O\66\3\2\2\2O:\3\2\2\2O>\3\2\2\2O?\3"+
		"\2\2\2OK\3\2\2\2P_\3\2\2\2QR\f\13\2\2RS\7\16\2\2S^\5\6\4\fTU\f\n\2\2U"+
		"V\7\17\2\2V^\5\6\4\13WX\f\t\2\2XY\7\20\2\2Y^\5\6\4\nZ[\f\b\2\2[\\\7\21"+
		"\2\2\\^\5\6\4\t]Q\3\2\2\2]T\3\2\2\2]W\3\2\2\2]Z\3\2\2\2^a\3\2\2\2_]\3"+
		"\2\2\2_`\3\2\2\2`\7\3\2\2\2a_\3\2\2\2bp\7\24\2\2cd\7\24\2\2de\7\4\2\2"+
		"ej\5\b\5\2fg\7\5\2\2gi\5\b\5\2hf\3\2\2\2il\3\2\2\2jh\3\2\2\2jk\3\2\2\2"+
		"km\3\2\2\2lj\3\2\2\2mn\7\6\2\2np\3\2\2\2ob\3\2\2\2oc\3\2\2\2p\t\3\2\2"+
		"\2\13\r#\60FO]_jo";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}