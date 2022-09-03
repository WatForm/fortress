// Generated from /u5/ozila/modeling/fortress/core/src/main/antlr4/fortress/inputs/FOFTPTP.g4 by ANTLR 4.9.2
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class FOFTPTPParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.9.2", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__0=1, T__1=2, T__2=3, T__3=4, T__4=5, T__5=6, T__6=7, T__7=8, T__8=9, 
		T__9=10, T__10=11, T__11=12, T__12=13, T__13=14, T__14=15, T__15=16, T__16=17, 
		T__17=18, SINGLE_QUOTED=19, ID=20, DEFINED_PROP=21, WS=22, COMMENT=23;
	public static final int
		RULE_spec = 0, RULE_line = 1, RULE_fof_formula = 2, RULE_name = 3, RULE_term = 4;
	private static String[] makeRuleNames() {
		return new String[] {
			"spec", "line", "fof_formula", "name", "term"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'fof'", "'('", "','", "')'", "'.'", "'include'", "'~'", "'!'", 
			"'['", "']'", "':'", "'?'", "'&'", "'|'", "'=>'", "'<=>'", "'='", "'!='"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, "SINGLE_QUOTED", "ID", "DEFINED_PROP", 
			"WS", "COMMENT"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
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
		public TerminalNode EOF() { return getToken(FOFTPTPParser.EOF, 0); }
		public List<LineContext> line() {
			return getRuleContexts(LineContext.class);
		}
		public LineContext line(int i) {
			return getRuleContext(LineContext.class,i);
		}
		public SpecContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_spec; }
	}

	public final SpecContext spec() throws RecognitionException {
		SpecContext _localctx = new SpecContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_spec);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(11); 
			_errHandler.sync(this);
			_la = _input.LA(1);
			do {
				{
				{
				setState(10);
				line();
				}
				}
				setState(13); 
				_errHandler.sync(this);
				_la = _input.LA(1);
			} while ( _la==T__0 || _la==T__5 );
			setState(15);
			match(EOF);
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

	public static class LineContext extends ParserRuleContext {
		public LineContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_line; }
	 
		public LineContext() { }
		public void copyFrom(LineContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class IncludeContext extends LineContext {
		public TerminalNode SINGLE_QUOTED() { return getToken(FOFTPTPParser.SINGLE_QUOTED, 0); }
		public IncludeContext(LineContext ctx) { copyFrom(ctx); }
	}
	public static class Fof_annotatedContext extends LineContext {
		public NameContext name() {
			return getRuleContext(NameContext.class,0);
		}
		public TerminalNode ID() { return getToken(FOFTPTPParser.ID, 0); }
		public Fof_formulaContext fof_formula() {
			return getRuleContext(Fof_formulaContext.class,0);
		}
		public Fof_annotatedContext(LineContext ctx) { copyFrom(ctx); }
	}

	public final LineContext line() throws RecognitionException {
		LineContext _localctx = new LineContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_line);
		try {
			setState(32);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__0:
				_localctx = new Fof_annotatedContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(17);
				match(T__0);
				setState(18);
				match(T__1);
				setState(19);
				name();
				setState(20);
				match(T__2);
				setState(21);
				match(ID);
				setState(22);
				match(T__2);
				setState(23);
				fof_formula(0);
				setState(24);
				match(T__3);
				setState(25);
				match(T__4);
				}
				break;
			case T__5:
				_localctx = new IncludeContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(27);
				match(T__5);
				setState(28);
				match(T__1);
				setState(29);
				match(SINGLE_QUOTED);
				setState(30);
				match(T__3);
				setState(31);
				match(T__4);
				}
				break;
			default:
				throw new NoViableAltException(this);
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
	public static class OrContext extends Fof_formulaContext {
		public List<Fof_formulaContext> fof_formula() {
			return getRuleContexts(Fof_formulaContext.class);
		}
		public Fof_formulaContext fof_formula(int i) {
			return getRuleContext(Fof_formulaContext.class,i);
		}
		public OrContext(Fof_formulaContext ctx) { copyFrom(ctx); }
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
	}
	public static class Defined_propContext extends Fof_formulaContext {
		public TerminalNode DEFINED_PROP() { return getToken(FOFTPTPParser.DEFINED_PROP, 0); }
		public Defined_propContext(Fof_formulaContext ctx) { copyFrom(ctx); }
	}
	public static class IffContext extends Fof_formulaContext {
		public List<Fof_formulaContext> fof_formula() {
			return getRuleContexts(Fof_formulaContext.class);
		}
		public Fof_formulaContext fof_formula(int i) {
			return getRuleContext(Fof_formulaContext.class,i);
		}
		public IffContext(Fof_formulaContext ctx) { copyFrom(ctx); }
	}
	public static class EqContext extends Fof_formulaContext {
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public EqContext(Fof_formulaContext ctx) { copyFrom(ctx); }
	}
	public static class ImpContext extends Fof_formulaContext {
		public List<Fof_formulaContext> fof_formula() {
			return getRuleContexts(Fof_formulaContext.class);
		}
		public Fof_formulaContext fof_formula(int i) {
			return getRuleContext(Fof_formulaContext.class,i);
		}
		public ImpContext(Fof_formulaContext ctx) { copyFrom(ctx); }
	}
	public static class NotContext extends Fof_formulaContext {
		public Fof_formulaContext fof_formula() {
			return getRuleContext(Fof_formulaContext.class,0);
		}
		public NotContext(Fof_formulaContext ctx) { copyFrom(ctx); }
	}
	public static class ParenContext extends Fof_formulaContext {
		public Fof_formulaContext fof_formula() {
			return getRuleContext(Fof_formulaContext.class,0);
		}
		public ParenContext(Fof_formulaContext ctx) { copyFrom(ctx); }
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
	}
	public static class AndContext extends Fof_formulaContext {
		public List<Fof_formulaContext> fof_formula() {
			return getRuleContexts(Fof_formulaContext.class);
		}
		public Fof_formulaContext fof_formula(int i) {
			return getRuleContext(Fof_formulaContext.class,i);
		}
		public AndContext(Fof_formulaContext ctx) { copyFrom(ctx); }
	}
	public static class PropContext extends Fof_formulaContext {
		public TerminalNode ID() { return getToken(FOFTPTPParser.ID, 0); }
		public PropContext(Fof_formulaContext ctx) { copyFrom(ctx); }
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
	}
	public static class NeqContext extends Fof_formulaContext {
		public List<TermContext> term() {
			return getRuleContexts(TermContext.class);
		}
		public TermContext term(int i) {
			return getRuleContext(TermContext.class,i);
		}
		public NeqContext(Fof_formulaContext ctx) { copyFrom(ctx); }
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
			setState(89);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,5,_ctx) ) {
			case 1:
				{
				_localctx = new NotContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;

				setState(35);
				match(T__6);
				setState(36);
				fof_formula(13);
				}
				break;
			case 2:
				{
				_localctx = new ForallContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(37);
				match(T__7);
				setState(38);
				match(T__8);
				setState(39);
				match(ID);
				setState(44);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__2) {
					{
					{
					setState(40);
					match(T__2);
					setState(41);
					match(ID);
					}
					}
					setState(46);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(47);
				match(T__9);
				setState(48);
				match(T__10);
				setState(49);
				fof_formula(12);
				}
				break;
			case 3:
				{
				_localctx = new ExistsContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(50);
				match(T__11);
				setState(51);
				match(T__8);
				setState(52);
				match(ID);
				setState(57);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__2) {
					{
					{
					setState(53);
					match(T__2);
					setState(54);
					match(ID);
					}
					}
					setState(59);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(60);
				match(T__9);
				setState(61);
				match(T__10);
				setState(62);
				fof_formula(11);
				}
				break;
			case 4:
				{
				_localctx = new EqContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(63);
				term();
				setState(64);
				match(T__16);
				setState(65);
				term();
				}
				break;
			case 5:
				{
				_localctx = new NeqContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(67);
				term();
				setState(68);
				match(T__17);
				setState(69);
				term();
				}
				break;
			case 6:
				{
				_localctx = new PropContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(71);
				match(ID);
				}
				break;
			case 7:
				{
				_localctx = new Defined_propContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(72);
				match(DEFINED_PROP);
				}
				break;
			case 8:
				{
				_localctx = new PredContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(73);
				match(ID);
				setState(74);
				match(T__1);
				setState(75);
				term();
				setState(80);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__2) {
					{
					{
					setState(76);
					match(T__2);
					setState(77);
					term();
					}
					}
					setState(82);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(83);
				match(T__3);
				}
				break;
			case 9:
				{
				_localctx = new ParenContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(85);
				match(T__1);
				setState(86);
				fof_formula(0);
				setState(87);
				match(T__3);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(105);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,7,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(103);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,6,_ctx) ) {
					case 1:
						{
						_localctx = new AndContext(new Fof_formulaContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_fof_formula);
						setState(91);
						if (!(precpred(_ctx, 10))) throw new FailedPredicateException(this, "precpred(_ctx, 10)");
						setState(92);
						match(T__12);
						setState(93);
						fof_formula(11);
						}
						break;
					case 2:
						{
						_localctx = new OrContext(new Fof_formulaContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_fof_formula);
						setState(94);
						if (!(precpred(_ctx, 9))) throw new FailedPredicateException(this, "precpred(_ctx, 9)");
						setState(95);
						match(T__13);
						setState(96);
						fof_formula(10);
						}
						break;
					case 3:
						{
						_localctx = new ImpContext(new Fof_formulaContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_fof_formula);
						setState(97);
						if (!(precpred(_ctx, 8))) throw new FailedPredicateException(this, "precpred(_ctx, 8)");
						setState(98);
						match(T__14);
						setState(99);
						fof_formula(9);
						}
						break;
					case 4:
						{
						_localctx = new IffContext(new Fof_formulaContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_fof_formula);
						setState(100);
						if (!(precpred(_ctx, 7))) throw new FailedPredicateException(this, "precpred(_ctx, 7)");
						setState(101);
						match(T__15);
						setState(102);
						fof_formula(8);
						}
						break;
					}
					} 
				}
				setState(107);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,7,_ctx);
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

	public static class NameContext extends ParserRuleContext {
		public TerminalNode ID() { return getToken(FOFTPTPParser.ID, 0); }
		public TerminalNode SINGLE_QUOTED() { return getToken(FOFTPTPParser.SINGLE_QUOTED, 0); }
		public NameContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_name; }
	}

	public final NameContext name() throws RecognitionException {
		NameContext _localctx = new NameContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_name);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(108);
			_la = _input.LA(1);
			if ( !(_la==SINGLE_QUOTED || _la==ID) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
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
	}
	public static class ConVarContext extends TermContext {
		public TerminalNode ID() { return getToken(FOFTPTPParser.ID, 0); }
		public ConVarContext(TermContext ctx) { copyFrom(ctx); }
	}

	public final TermContext term() throws RecognitionException {
		TermContext _localctx = new TermContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_term);
		int _la;
		try {
			setState(123);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,9,_ctx) ) {
			case 1:
				_localctx = new ConVarContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(110);
				match(ID);
				}
				break;
			case 2:
				_localctx = new ApplyContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(111);
				match(ID);
				setState(112);
				match(T__1);
				setState(113);
				term();
				setState(118);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__2) {
					{
					{
					setState(114);
					match(T__2);
					setState(115);
					term();
					}
					}
					setState(120);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(121);
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
			return precpred(_ctx, 10);
		case 1:
			return precpred(_ctx, 9);
		case 2:
			return precpred(_ctx, 8);
		case 3:
			return precpred(_ctx, 7);
		}
		return true;
	}

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3\31\u0080\4\2\t\2"+
		"\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\3\2\6\2\16\n\2\r\2\16\2\17\3\2\3\2\3"+
		"\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\5\3#\n\3\3"+
		"\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\7\4-\n\4\f\4\16\4\60\13\4\3\4\3\4\3\4\3"+
		"\4\3\4\3\4\3\4\3\4\7\4:\n\4\f\4\16\4=\13\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4"+
		"\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\7\4Q\n\4\f\4\16\4T\13\4\3"+
		"\4\3\4\3\4\3\4\3\4\3\4\5\4\\\n\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3"+
		"\4\3\4\3\4\7\4j\n\4\f\4\16\4m\13\4\3\5\3\5\3\6\3\6\3\6\3\6\3\6\3\6\7\6"+
		"w\n\6\f\6\16\6z\13\6\3\6\3\6\5\6~\n\6\3\6\2\3\6\7\2\4\6\b\n\2\3\3\2\25"+
		"\26\2\u008d\2\r\3\2\2\2\4\"\3\2\2\2\6[\3\2\2\2\bn\3\2\2\2\n}\3\2\2\2\f"+
		"\16\5\4\3\2\r\f\3\2\2\2\16\17\3\2\2\2\17\r\3\2\2\2\17\20\3\2\2\2\20\21"+
		"\3\2\2\2\21\22\7\2\2\3\22\3\3\2\2\2\23\24\7\3\2\2\24\25\7\4\2\2\25\26"+
		"\5\b\5\2\26\27\7\5\2\2\27\30\7\26\2\2\30\31\7\5\2\2\31\32\5\6\4\2\32\33"+
		"\7\6\2\2\33\34\7\7\2\2\34#\3\2\2\2\35\36\7\b\2\2\36\37\7\4\2\2\37 \7\25"+
		"\2\2 !\7\6\2\2!#\7\7\2\2\"\23\3\2\2\2\"\35\3\2\2\2#\5\3\2\2\2$%\b\4\1"+
		"\2%&\7\t\2\2&\\\5\6\4\17\'(\7\n\2\2()\7\13\2\2).\7\26\2\2*+\7\5\2\2+-"+
		"\7\26\2\2,*\3\2\2\2-\60\3\2\2\2.,\3\2\2\2./\3\2\2\2/\61\3\2\2\2\60.\3"+
		"\2\2\2\61\62\7\f\2\2\62\63\7\r\2\2\63\\\5\6\4\16\64\65\7\16\2\2\65\66"+
		"\7\13\2\2\66;\7\26\2\2\678\7\5\2\28:\7\26\2\29\67\3\2\2\2:=\3\2\2\2;9"+
		"\3\2\2\2;<\3\2\2\2<>\3\2\2\2=;\3\2\2\2>?\7\f\2\2?@\7\r\2\2@\\\5\6\4\r"+
		"AB\5\n\6\2BC\7\23\2\2CD\5\n\6\2D\\\3\2\2\2EF\5\n\6\2FG\7\24\2\2GH\5\n"+
		"\6\2H\\\3\2\2\2I\\\7\26\2\2J\\\7\27\2\2KL\7\26\2\2LM\7\4\2\2MR\5\n\6\2"+
		"NO\7\5\2\2OQ\5\n\6\2PN\3\2\2\2QT\3\2\2\2RP\3\2\2\2RS\3\2\2\2SU\3\2\2\2"+
		"TR\3\2\2\2UV\7\6\2\2V\\\3\2\2\2WX\7\4\2\2XY\5\6\4\2YZ\7\6\2\2Z\\\3\2\2"+
		"\2[$\3\2\2\2[\'\3\2\2\2[\64\3\2\2\2[A\3\2\2\2[E\3\2\2\2[I\3\2\2\2[J\3"+
		"\2\2\2[K\3\2\2\2[W\3\2\2\2\\k\3\2\2\2]^\f\f\2\2^_\7\17\2\2_j\5\6\4\r`"+
		"a\f\13\2\2ab\7\20\2\2bj\5\6\4\fcd\f\n\2\2de\7\21\2\2ej\5\6\4\13fg\f\t"+
		"\2\2gh\7\22\2\2hj\5\6\4\ni]\3\2\2\2i`\3\2\2\2ic\3\2\2\2if\3\2\2\2jm\3"+
		"\2\2\2ki\3\2\2\2kl\3\2\2\2l\7\3\2\2\2mk\3\2\2\2no\t\2\2\2o\t\3\2\2\2p"+
		"~\7\26\2\2qr\7\26\2\2rs\7\4\2\2sx\5\n\6\2tu\7\5\2\2uw\5\n\6\2vt\3\2\2"+
		"\2wz\3\2\2\2xv\3\2\2\2xy\3\2\2\2y{\3\2\2\2zx\3\2\2\2{|\7\6\2\2|~\3\2\2"+
		"\2}p\3\2\2\2}q\3\2\2\2~\13\3\2\2\2\f\17\".;R[ikx}";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}