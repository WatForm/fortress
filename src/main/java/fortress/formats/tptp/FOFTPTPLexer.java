// Generated from FOFTPTP.g4 by ANTLR 4.5.2
package fortress.formats.tptp;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class FOFTPTPLexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.5.2", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__0=1, T__1=2, T__2=3, T__3=4, T__4=5, T__5=6, T__6=7, T__7=8, T__8=9, 
		T__9=10, T__10=11, T__11=12, T__12=13, T__13=14, T__14=15, T__15=16, T__16=17, 
		ID=18, WS=19, COMMENT=20;
	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	public static final String[] ruleNames = {
		"T__0", "T__1", "T__2", "T__3", "T__4", "T__5", "T__6", "T__7", "T__8", 
		"T__9", "T__10", "T__11", "T__12", "T__13", "T__14", "T__15", "T__16", 
		"ID", "WS", "COMMENT"
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


	public FOFTPTPLexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "FOFTPTP.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public String[] getModeNames() { return modeNames; }

	@Override
	public ATN getATN() { return _ATN; }

	public static final String _serializedATN =
		"\3\u0430\ud6d1\u8206\uad2d\u4417\uaef1\u8d80\uaadd\2\26m\b\1\4\2\t\2\4"+
		"\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13\t"+
		"\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22"+
		"\4\23\t\23\4\24\t\24\4\25\t\25\3\2\3\2\3\2\3\2\3\3\3\3\3\4\3\4\3\5\3\5"+
		"\3\6\3\6\3\7\3\7\3\b\3\b\3\t\3\t\3\n\3\n\3\13\3\13\3\f\3\f\3\r\3\r\3\16"+
		"\3\16\3\17\3\17\3\17\3\20\3\20\3\20\3\20\3\21\3\21\3\22\3\22\3\22\3\23"+
		"\3\23\7\23V\n\23\f\23\16\23Y\13\23\3\24\3\24\3\24\3\24\3\25\3\25\7\25"+
		"a\n\25\f\25\16\25d\13\25\3\25\5\25g\n\25\3\25\5\25j\n\25\3\25\3\25\2\2"+
		"\26\3\3\5\4\7\5\t\6\13\7\r\b\17\t\21\n\23\13\25\f\27\r\31\16\33\17\35"+
		"\20\37\21!\22#\23%\24\'\25)\26\3\2\6\5\2C\\aac|\6\2\62;C\\aac|\5\2\13"+
		"\f\17\17\"\"\4\2\f\f\17\17p\2\3\3\2\2\2\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3"+
		"\2\2\2\2\13\3\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2\2\23\3\2\2\2"+
		"\2\25\3\2\2\2\2\27\3\2\2\2\2\31\3\2\2\2\2\33\3\2\2\2\2\35\3\2\2\2\2\37"+
		"\3\2\2\2\2!\3\2\2\2\2#\3\2\2\2\2%\3\2\2\2\2\'\3\2\2\2\2)\3\2\2\2\3+\3"+
		"\2\2\2\5/\3\2\2\2\7\61\3\2\2\2\t\63\3\2\2\2\13\65\3\2\2\2\r\67\3\2\2\2"+
		"\179\3\2\2\2\21;\3\2\2\2\23=\3\2\2\2\25?\3\2\2\2\27A\3\2\2\2\31C\3\2\2"+
		"\2\33E\3\2\2\2\35G\3\2\2\2\37J\3\2\2\2!N\3\2\2\2#P\3\2\2\2%S\3\2\2\2\'"+
		"Z\3\2\2\2)^\3\2\2\2+,\7h\2\2,-\7q\2\2-.\7h\2\2.\4\3\2\2\2/\60\7*\2\2\60"+
		"\6\3\2\2\2\61\62\7.\2\2\62\b\3\2\2\2\63\64\7+\2\2\64\n\3\2\2\2\65\66\7"+
		"\60\2\2\66\f\3\2\2\2\678\7\u0080\2\28\16\3\2\2\29:\7#\2\2:\20\3\2\2\2"+
		";<\7]\2\2<\22\3\2\2\2=>\7_\2\2>\24\3\2\2\2?@\7<\2\2@\26\3\2\2\2AB\7A\2"+
		"\2B\30\3\2\2\2CD\7(\2\2D\32\3\2\2\2EF\7~\2\2F\34\3\2\2\2GH\7?\2\2HI\7"+
		"@\2\2I\36\3\2\2\2JK\7>\2\2KL\7?\2\2LM\7@\2\2M \3\2\2\2NO\7?\2\2O\"\3\2"+
		"\2\2PQ\7#\2\2QR\7?\2\2R$\3\2\2\2SW\t\2\2\2TV\t\3\2\2UT\3\2\2\2VY\3\2\2"+
		"\2WU\3\2\2\2WX\3\2\2\2X&\3\2\2\2YW\3\2\2\2Z[\t\4\2\2[\\\3\2\2\2\\]\b\24"+
		"\2\2](\3\2\2\2^b\7\'\2\2_a\n\5\2\2`_\3\2\2\2ad\3\2\2\2b`\3\2\2\2bc\3\2"+
		"\2\2ci\3\2\2\2db\3\2\2\2eg\7\17\2\2fe\3\2\2\2fg\3\2\2\2gh\3\2\2\2hj\7"+
		"\f\2\2if\3\2\2\2ij\3\2\2\2jk\3\2\2\2kl\b\25\2\2l*\3\2\2\2\7\2Wbfi\3\b"+
		"\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}