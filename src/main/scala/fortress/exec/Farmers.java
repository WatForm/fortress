package fortress.exec;

import fortress.msfol.*;
import fortress.modelfind.*;

import java.util.List;

public final class Farmers {

	public static void main(String[] args) throws Exception {

		Theory theory = Theory.empty();
		Sort x2 = Sort.mkSortConst("sortthis/Time");
		theory = theory.withSort(x2);

		Sort x3 = Sort.mkSortConst("sortthis/Process");
		theory = theory.withSort(x3);

		Sort x4 = Sort.mkSortConst("sortTO/Ord");
		theory = theory.withSort(x4);

		Sort x5 = Sort.mkSortConst("sortPO/Ord");
		theory = theory.withSort(x5);

		theory = theory.withFunctionDeclaration(FuncDecl.mkFuncDecl("this/Time", x2, Sort.Bool()));

		theory = theory.withFunctionDeclaration(FuncDecl.mkFuncDecl("this/Process", x3, Sort.Bool()));

		theory = theory.withFunctionDeclaration(FuncDecl.mkFuncDecl("TO/Ord", x4, Sort.Bool()));

		theory = theory.withFunctionDeclaration(FuncDecl.mkFuncDecl("PO/Ord", x5, Sort.Bool()));

		theory = theory.withFunctionDeclaration(FuncDecl.mkFuncDecl("this/Process.succ", x3, x3, Sort.Bool()));

		theory = theory.withFunctionDeclaration(FuncDecl.mkFuncDecl("this/Process.toSend", x3, x3, x2, Sort.Bool()));

		theory = theory.withFunctionDeclaration(FuncDecl.mkFuncDecl("this/Process.elected", x3, x2, Sort.Bool()));

		theory = theory.withFunctionDeclaration(FuncDecl.mkFuncDecl("TO/Ord.First", x4, x2, Sort.Bool()));

		theory = theory.withFunctionDeclaration(FuncDecl.mkFuncDecl("TO/Ord.Next", x4, x2, x2, Sort.Bool()));

		theory = theory.withFunctionDeclaration(FuncDecl.mkFuncDecl("PO/Ord.First", x5, x3, Sort.Bool()));

		theory = theory.withFunctionDeclaration(FuncDecl.mkFuncDecl("PO/Ord.Next", x5, x3, x3, Sort.Bool()));

		theory = theory.withFunctionDeclaration(FuncDecl.mkFuncDecl("func_0", x2, x3, Sort.Bool()));

		theory = theory.withFunctionDeclaration(FuncDecl.mkFuncDecl("func_1", x3, x3, Sort.Bool()));

		Term x8 = Term.mkDomainElement(1, x4);
		Term x9 = Term.mkDomainElement(9, x2);
		Term x7 = Term.mkApp("TO/Ord.First", x8, x9);
		Term x6 = Term.mkNot(x7);
		theory = theory.withAxiom(x6);

		Term x11 = Term.mkDomainElement(1, x5);
		Term x12 = Term.mkDomainElement(1, x3);
		Term x13 = Term.mkDomainElement(2, x3);
		Term x10 = Term.mkApp("PO/Ord.Next", x11, x12, x13);
		theory = theory.withAxiom(x10);

		Term x16 = Term.mkDomainElement(5, x2);
		Term x17 = Term.mkDomainElement(3, x2);
		Term x15 = Term.mkApp("TO/Ord.Next", x8, x16, x17);
		Term x14 = Term.mkNot(x15);
		theory = theory.withAxiom(x14);

		Term x20 = Term.mkDomainElement(4, x2);
		Term x21 = Term.mkDomainElement(7, x2);
		Term x19 = Term.mkApp("TO/Ord.Next", x8, x20, x21);
		Term x18 = Term.mkNot(x19);
		theory = theory.withAxiom(x18);

		Term x23 = Term.mkDomainElement(3, x3);
		Term x22 = Term.mkApp("PO/Ord.Next", x11, x13, x23);
		theory = theory.withAxiom(x22);

		Term x26 = Term.mkDomainElement(8, x2);
		Term x25 = Term.mkApp("TO/Ord.Next", x8, x26, x21);
		Term x24 = Term.mkNot(x25);
		theory = theory.withAxiom(x24);

		Term x29 = Term.mkDomainElement(12, x2);
		Term x28 = Term.mkApp("TO/Ord.Next", x8, x16, x29);
		Term x27 = Term.mkNot(x28);
		theory = theory.withAxiom(x27);

		Term x32 = Term.mkDomainElement(10, x2);
		Term x31 = Term.mkApp("TO/Ord.Next", x8, x32, x16);
		Term x30 = Term.mkNot(x31);
		theory = theory.withAxiom(x30);

		Term x34 = Term.mkApp("TO/Ord.First", x8, x26);
		Term x33 = Term.mkNot(x34);
		theory = theory.withAxiom(x33);

		Term x36 = Term.mkApp("TO/Ord.Next", x8, x17, x9);
		Term x35 = Term.mkNot(x36);
		theory = theory.withAxiom(x35);

		Term x39 = Term.mkDomainElement(2, x2);
		Term x38 = Term.mkApp("TO/Ord.Next", x8, x39, x21);
		Term x37 = Term.mkNot(x38);
		theory = theory.withAxiom(x37);

		Term x41 = Term.mkApp("TO/Ord.First", x8, x39);
		Term x40 = Term.mkNot(x41);
		theory = theory.withAxiom(x40);

		Term x44 = Term.mkDomainElement(6, x2);
		Term x43 = Term.mkApp("TO/Ord.Next", x8, x44, x26);
		Term x42 = Term.mkNot(x43);
		theory = theory.withAxiom(x42);

		Term x47 = Term.mkDomainElement(13, x2);
		Term x46 = Term.mkApp("TO/Ord.Next", x8, x16, x47);
		Term x45 = Term.mkNot(x46);
		theory = theory.withAxiom(x45);

		Term x49 = Term.mkApp("TO/Ord.Next", x8, x29, x16);
		Term x48 = Term.mkNot(x49);
		theory = theory.withAxiom(x48);

		Var x51 = Term.mkVar("var_31");
		Var x52 = Term.mkVar("var_32");
		Term x54 = Term.mkApp("this/Process.elected", x51, x52);
		Term x56 = Term.mkApp("this/Process", x51);
		Term x57 = Term.mkApp("this/Time", x52);
		Term x55 = Term.mkAnd(x56, x57);
		Term x53 = Term.mkImp(x54, x55);
		Term x50 = Term.mkForall(List.of(x51.of(x3), x52.of(x2)), x53);
		theory = theory.withAxiom(x50);

		Term x59 = Term.mkApp("TO/Ord.Next", x8, x26, x39);
		Term x58 = Term.mkNot(x59);
		theory = theory.withAxiom(x58);

		Term x61 = Term.mkApp("TO/Ord.Next", x8, x26, x47);
		Term x60 = Term.mkNot(x61);
		theory = theory.withAxiom(x60);

		Term x63 = Term.mkApp("TO/Ord.Next", x8, x29, x21);
		Term x62 = Term.mkNot(x63);
		theory = theory.withAxiom(x62);

		Term x66 = Term.mkDomainElement(11, x2);
		Term x65 = Term.mkApp("TO/Ord.Next", x8, x66, x9);
		Term x64 = Term.mkNot(x65);
		theory = theory.withAxiom(x64);

		Term x68 = Term.mkApp("TO/Ord.Next", x8, x26, x17);
		Term x67 = Term.mkNot(x68);
		theory = theory.withAxiom(x67);

		Term x69 = Term.mkApp("TO/Ord.Next", x8, x32, x66);
		theory = theory.withAxiom(x69);

		Term x71 = Term.mkApp("TO/Ord.Next", x8, x9, x26);
		Term x70 = Term.mkNot(x71);
		theory = theory.withAxiom(x70);

		Term x73 = Term.mkApp("TO/Ord.First", x8, x17);
		Term x72 = Term.mkNot(x73);
		theory = theory.withAxiom(x72);

		Term x75 = Term.mkApp("TO/Ord.Next", x8, x16, x16);
		Term x74 = Term.mkNot(x75);
		theory = theory.withAxiom(x74);

		Term x77 = Term.mkApp("TO/Ord.Next", x8, x9, x29);
		Term x76 = Term.mkNot(x77);
		theory = theory.withAxiom(x76);

		Term x80 = Term.mkDomainElement(1, x2);
		Term x79 = Term.mkApp("TO/Ord.Next", x8, x17, x80);
		Term x78 = Term.mkNot(x79);
		theory = theory.withAxiom(x78);

		Term x82 = Term.mkApp("TO/Ord.Next", x8, x80, x80);
		Term x81 = Term.mkNot(x82);
		theory = theory.withAxiom(x81);

		Term x84 = Term.mkApp("TO/Ord.Next", x8, x66, x44);
		Term x83 = Term.mkNot(x84);
		theory = theory.withAxiom(x83);

		Term x86 = Term.mkApp("TO/Ord.Next", x8, x80, x44);
		Term x85 = Term.mkNot(x86);
		theory = theory.withAxiom(x85);

		Term x88 = Term.mkApp("TO/Ord.Next", x8, x47, x80);
		Term x87 = Term.mkNot(x88);
		theory = theory.withAxiom(x87);

		Term x90 = Term.mkApp("TO/Ord.Next", x8, x26, x66);
		Term x89 = Term.mkNot(x90);
		theory = theory.withAxiom(x89);

		Term x92 = Term.mkApp("TO/Ord.Next", x8, x9, x80);
		Term x91 = Term.mkNot(x92);
		theory = theory.withAxiom(x91);

		Term x94 = Term.mkApp("TO/Ord.Next", x8, x9, x16);
		Term x93 = Term.mkNot(x94);
		theory = theory.withAxiom(x93);

		Term x96 = Term.mkApp("TO/Ord.Next", x8, x16, x66);
		Term x95 = Term.mkNot(x96);
		theory = theory.withAxiom(x95);

		Term x98 = Term.mkApp("TO/Ord.Next", x8, x80, x66);
		Term x97 = Term.mkNot(x98);
		theory = theory.withAxiom(x97);

		Term x100 = Term.mkApp("TO/Ord.Next", x8, x44, x47);
		Term x99 = Term.mkNot(x100);
		theory = theory.withAxiom(x99);

		Term x102 = Term.mkApp("TO/Ord.Next", x8, x16, x39);
		Term x101 = Term.mkNot(x102);
		theory = theory.withAxiom(x101);

		Var x104 = Term.mkVar("var_28");
		Var x105 = Term.mkVar("var_29");
		Var x106 = Term.mkVar("var_30");
		Term x108 = Term.mkApp("this/Process.toSend", x104, x105, x106);
		Term x111 = Term.mkApp("this/Process", x104);
		Term x112 = Term.mkApp("this/Process", x105);
		Term x110 = Term.mkAnd(x111, x112);
		Term x113 = Term.mkApp("this/Time", x106);
		Term x109 = Term.mkAnd(x110, x113);
		Term x107 = Term.mkImp(x108, x109);
		Term x103 = Term.mkForall(List.of(x104.of(x3), x105.of(x3), x106.of(x2)), x107);
		theory = theory.withAxiom(x103);

		Term x115 = Term.mkApp("TO/Ord.Next", x8, x39, x44);
		Term x114 = Term.mkNot(x115);
		theory = theory.withAxiom(x114);

		Term x117 = Term.mkApp("TO/Ord.First", x8, x20);
		Term x116 = Term.mkNot(x117);
		theory = theory.withAxiom(x116);

		Term x119 = Term.mkApp("TO/Ord.Next", x8, x44, x20);
		Term x118 = Term.mkNot(x119);
		theory = theory.withAxiom(x118);

		Var x121 = Term.mkVar("looplessPath_this_0");
		Term x123 = Term.mkApp("this/Process", x121);
		Var x127 = Term.mkVar("var_44");
		Term x128 = Term.mkApp("this/Process.succ", x121, x127);
		Term x126 = Term.mkExists(List.of(x127.of(x3)), x128);
		Var x130 = Term.mkVar("var_45");
		Term x132 = Term.mkApp("this/Process.succ", x121, x130);
		Term x135 = Term.mkEq(x127, x130);
		Term x134 = Term.mkImp(x128, x135);
		Term x133 = Term.mkForall(List.of(x127.of(x3)), x134);
		Term x131 = Term.mkImp(x132, x133);
		Term x129 = Term.mkForall(List.of(x130.of(x3)), x131);
		Term x125 = Term.mkAnd(x126, x129);
		Var x137 = Term.mkVar("var_43");
		Term x139 = Term.mkApp("this/Process.succ", x121, x137);
		Term x140 = Term.mkApp("this/Process", x137);
		Term x138 = Term.mkImp(x139, x140);
		Term x136 = Term.mkForall(List.of(x137.of(x3)), x138);
		Term x124 = Term.mkAnd(x125, x136);
		Term x122 = Term.mkImp(x123, x124);
		Term x120 = Term.mkForall(List.of(x121.of(x3)), x122);
		theory = theory.withAxiom(x120);

		Var x142 = Term.mkVar("var_49");
		Var x145 = Term.mkVar("var_50");
		Term x147 = Term.mkApp("TO/Ord", x145);
		Term x148 = Term.mkApp("TO/Ord.First", x145, x142);
		Term x146 = Term.mkAnd(x147, x148);
		Term x144 = Term.mkExists(List.of(x145.of(x4)), x146);
		Term x149 = Term.mkApp("this/Time", x142);
		Term x143 = Term.mkImp(x144, x149);
		Term x141 = Term.mkForall(List.of(x142.of(x2)), x143);
		theory = theory.withAxiom(x141);

		Term x151 = Term.mkApp("TO/Ord.Next", x8, x29, x9);
		Term x150 = Term.mkNot(x151);
		theory = theory.withAxiom(x150);

		Term x153 = Term.mkApp("TO/Ord.Next", x8, x39, x9);
		Term x152 = Term.mkNot(x153);
		theory = theory.withAxiom(x152);

		Term x155 = Term.mkApp("TO/Ord.Next", x8, x21, x44);
		Term x154 = Term.mkNot(x155);
		theory = theory.withAxiom(x154);

		Term x156 = Term.mkApp("TO/Ord.Next", x8, x66, x29);
		theory = theory.withAxiom(x156);

		Term x158 = Term.mkApp("TO/Ord.Next", x8, x66, x80);
		Term x157 = Term.mkNot(x158);
		theory = theory.withAxiom(x157);

		Term x160 = Term.mkApp("TO/Ord.Next", x8, x29, x20);
		Term x159 = Term.mkNot(x160);
		theory = theory.withAxiom(x159);

		Term x162 = Term.mkApp("TO/Ord.Next", x8, x29, x39);
		Term x161 = Term.mkNot(x162);
		theory = theory.withAxiom(x161);

		Term x164 = Term.mkApp("TO/Ord.Next", x8, x20, x47);
		Term x163 = Term.mkNot(x164);
		theory = theory.withAxiom(x163);

		Term x166 = Term.mkApp("TO/Ord.Next", x8, x16, x20);
		Term x165 = Term.mkNot(x166);
		theory = theory.withAxiom(x165);

		Term x168 = Term.mkApp("TO/Ord.Next", x8, x39, x20);
		Term x167 = Term.mkNot(x168);
		theory = theory.withAxiom(x167);

		Var x170 = Term.mkVar("looplessPath_t_0");
		Term x173 = Term.mkApp("this/Time", x170);
		Var x176 = Term.mkVar("var_63");
		Term x178 = Term.mkApp("TO/Ord", x176);
		Term x179 = Term.mkApp("TO/Ord.First", x176, x170);
		Term x177 = Term.mkAnd(x178, x179);
		Term x175 = Term.mkExists(List.of(x176.of(x4)), x177);
		Term x174 = Term.mkNot(x175);
		Term x172 = Term.mkAnd(x173, x174);
		Var x181 = Term.mkVar("var_64");
		Term x183 = Term.mkApp("this/Process.elected", x181, x170);
		Term x184 = Term.mkApp("func_0", x170, x181);
		Term x182 = Term.mkIff(x183, x184);
		Term x180 = Term.mkForall(List.of(x181.of(x3)), x182);
		Term x171 = Term.mkImp(x172, x180);
		Term x169 = Term.mkForall(List.of(x170.of(x2)), x171);
		theory = theory.withAxiom(x169);

		Term x186 = Term.mkApp("TO/Ord.Next", x8, x39, x66);
		Term x185 = Term.mkNot(x186);
		theory = theory.withAxiom(x185);

		Term x188 = Term.mkApp("TO/Ord.Next", x8, x17, x26);
		Term x187 = Term.mkNot(x188);
		theory = theory.withAxiom(x187);

		Term x190 = Term.mkApp("TO/Ord.Next", x8, x17, x16);
		Term x189 = Term.mkNot(x190);
		theory = theory.withAxiom(x189);

		Var x192 = Term.mkVar("looplessPath_p_0");
		Term x194 = Term.mkApp("this/Process", x192);
		Var x196 = Term.mkVar("var_59");
		Term x198 = Term.mkApp("this/Process", x196);
		Term x199 = Term.mkClosure((App) Term.mkApp("this/Process.succ", x192, x196), x192, x196);
		Term x197 = Term.mkImp(x198, x199);
		Term x195 = Term.mkForall(List.of(x196.of(x3)), x197);
		Term x193 = Term.mkImp(x194, x195);
		Term x191 = Term.mkForall(List.of(x192.of(x3)), x193);
		theory = theory.withAxiom(x191);

		Term x201 = Term.mkApp("TO/Ord.Next", x8, x32, x32);
		Term x200 = Term.mkNot(x201);
		theory = theory.withAxiom(x200);

		Term x203 = Term.mkApp("TO/Ord.Next", x8, x47, x16);
		Term x202 = Term.mkNot(x203);
		theory = theory.withAxiom(x202);

		Var x205 = Term.mkVar("var_65");
		Var x206 = Term.mkVar("looplessPath_p");
		Term x208 = Term.mkApp("this/Process", x206);
		Term x210 = Term.mkApp("func_0", x205, x206);
		Var x212 = Term.mkVar("var_66");
		Term x214 = Term.mkEq(x212, x206);
		Term x216 = Term.mkApp("this/Process.toSend", x206, x212, x205);
		Var x219 = Term.mkVar("var_67");
		Term x221 = Term.mkApp("this/Process.toSend", x206, x212, x219);
		Var x223 = Term.mkVar("var_68");
		Term x225 = Term.mkApp("TO/Ord", x223);
		Term x226 = Term.mkApp("TO/Ord.Next", x223, x219, x205);
		Term x224 = Term.mkAnd(x225, x226);
		Term x222 = Term.mkExists(List.of(x223.of(x4)), x224);
		Term x220 = Term.mkAnd(x221, x222);
		Term x218 = Term.mkExists(List.of(x219.of(x2)), x220);
		Term x217 = Term.mkNot(x218);
		Term x215 = Term.mkAnd(x216, x217);
		Term x213 = Term.mkImp(x214, x215);
		Term x211 = Term.mkForall(List.of(x212.of(x3)), x213);
		Term x209 = Term.mkIff(x210, x211);
		Term x207 = Term.mkImp(x208, x209);
		Term x204 = Term.mkForall(List.of(x205.of(x2), x206.of(x3)), x207);
		theory = theory.withAxiom(x204);

		Term x228 = Term.mkApp("TO/Ord.Next", x8, x26, x44);
		Term x227 = Term.mkNot(x228);
		theory = theory.withAxiom(x227);

		Var x230 = Term.mkVar("var_51");
		Var x231 = Term.mkVar("var_52");
		Var x234 = Term.mkVar("var_53");
		Term x236 = Term.mkApp("TO/Ord", x234);
		Term x237 = Term.mkApp("TO/Ord.Next", x234, x230, x231);
		Term x235 = Term.mkAnd(x236, x237);
		Term x233 = Term.mkExists(List.of(x234.of(x4)), x235);
		Term x239 = Term.mkApp("this/Time", x230);
		Term x240 = Term.mkApp("this/Time", x231);
		Term x238 = Term.mkAnd(x239, x240);
		Term x232 = Term.mkImp(x233, x238);
		Term x229 = Term.mkForall(List.of(x230.of(x2), x231.of(x2)), x232);
		theory = theory.withAxiom(x229);

		Term x242 = Term.mkApp("TO/Ord.Next", x8, x17, x32);
		Term x241 = Term.mkNot(x242);
		theory = theory.withAxiom(x241);

		Term x244 = Term.mkApp("TO/Ord.Next", x8, x20, x66);
		Term x243 = Term.mkNot(x244);
		theory = theory.withAxiom(x243);

		Term x246 = Term.mkApp("TO/Ord.Next", x8, x47, x17);
		Term x245 = Term.mkNot(x246);
		theory = theory.withAxiom(x245);

		Term x248 = Term.mkApp("TO/Ord.Next", x8, x21, x66);
		Term x247 = Term.mkNot(x248);
		theory = theory.withAxiom(x247);

		Term x250 = Term.mkApp("TO/Ord.Next", x8, x66, x16);
		Term x249 = Term.mkNot(x250);
		theory = theory.withAxiom(x249);

		Term x251 = Term.mkApp("TO/Ord.Next", x8, x80, x39);
		theory = theory.withAxiom(x251);

		Term x253 = Term.mkApp("TO/Ord.Next", x8, x32, x21);
		Term x252 = Term.mkNot(x253);
		theory = theory.withAxiom(x252);

		Term x255 = Term.mkApp("TO/Ord.Next", x8, x39, x26);
		Term x254 = Term.mkNot(x255);
		theory = theory.withAxiom(x254);

		Term x257 = Term.mkApp("TO/Ord.Next", x8, x26, x20);
		Term x256 = Term.mkNot(x257);
		theory = theory.withAxiom(x256);

		Term x259 = Term.mkApp("TO/Ord.Next", x8, x17, x39);
		Term x258 = Term.mkNot(x259);
		theory = theory.withAxiom(x258);

		Term x261 = Term.mkApp("PO/Ord.First", x11, x13);
		Term x260 = Term.mkNot(x261);
		theory = theory.withAxiom(x260);

		Var x263 = Term.mkVar("var_26");
		Var x264 = Term.mkVar("var_27");
		Term x266 = Term.mkApp("this/Process.succ", x263, x264);
		Term x268 = Term.mkApp("this/Process", x263);
		Term x269 = Term.mkApp("this/Process", x264);
		Term x267 = Term.mkAnd(x268, x269);
		Term x265 = Term.mkImp(x266, x267);
		Term x262 = Term.mkForall(List.of(x263.of(x3), x264.of(x3)), x265);
		theory = theory.withAxiom(x262);

		Term x271 = Term.mkApp("TO/Ord.Next", x8, x20, x26);
		Term x270 = Term.mkNot(x271);
		theory = theory.withAxiom(x270);

		Term x273 = Term.mkApp("TO/Ord.Next", x8, x9, x39);
		Term x272 = Term.mkNot(x273);
		theory = theory.withAxiom(x272);

		Term x275 = Term.mkApp("TO/Ord.Next", x8, x16, x80);
		Term x274 = Term.mkNot(x275);
		theory = theory.withAxiom(x274);

		Term x277 = Term.mkApp("TO/Ord.Next", x8, x29, x26);
		Term x276 = Term.mkNot(x277);
		theory = theory.withAxiom(x276);

		Term x279 = Term.mkApp("TO/Ord.First", x8, x21);
		Term x278 = Term.mkNot(x279);
		theory = theory.withAxiom(x278);

		Var x281 = Term.mkVar("var_56");
		Var x282 = Term.mkVar("var_57");
		Var x285 = Term.mkVar("var_58");
		Term x287 = Term.mkApp("PO/Ord", x285);
		Term x288 = Term.mkApp("PO/Ord.Next", x285, x281, x282);
		Term x286 = Term.mkAnd(x287, x288);
		Term x284 = Term.mkExists(List.of(x285.of(x5)), x286);
		Term x290 = Term.mkApp("this/Process", x281);
		Term x291 = Term.mkApp("this/Process", x282);
		Term x289 = Term.mkAnd(x290, x291);
		Term x283 = Term.mkImp(x284, x289);
		Term x280 = Term.mkForall(List.of(x281.of(x3), x282.of(x3)), x283);
		theory = theory.withAxiom(x280);

		Var x293 = Term.mkVar("init_p_0");
		Term x295 = Term.mkApp("this/Process", x293);
		Var x297 = Term.mkVar("var_69");
		Term x299 = Term.mkEq(x297, x293);
		Var x301 = Term.mkVar("var_70");
		Term x303 = Term.mkApp("this/Process.toSend", x293, x297, x301);
		Var x305 = Term.mkVar("var_71");
		Term x307 = Term.mkApp("TO/Ord", x305);
		Term x308 = Term.mkApp("TO/Ord.First", x305, x301);
		Term x306 = Term.mkAnd(x307, x308);
		Term x304 = Term.mkExists(List.of(x305.of(x4)), x306);
		Term x302 = Term.mkAnd(x303, x304);
		Term x300 = Term.mkExists(List.of(x301.of(x2)), x302);
		Term x298 = Term.mkIff(x299, x300);
		Term x296 = Term.mkForall(List.of(x297.of(x3)), x298);
		Term x294 = Term.mkImp(x295, x296);
		Term x292 = Term.mkForall(List.of(x293.of(x3)), x294);
		theory = theory.withAxiom(x292);

		Term x310 = Term.mkApp("TO/Ord.Next", x8, x21, x80);
		Term x309 = Term.mkNot(x310);
		theory = theory.withAxiom(x309);

		Term x312 = Term.mkApp("TO/Ord.Next", x8, x66, x26);
		Term x311 = Term.mkNot(x312);
		theory = theory.withAxiom(x311);

		Term x314 = Term.mkApp("PO/Ord.First", x11, x23);
		Term x313 = Term.mkNot(x314);
		theory = theory.withAxiom(x313);

		Term x316 = Term.mkApp("TO/Ord.Next", x8, x32, x47);
		Term x315 = Term.mkNot(x316);
		theory = theory.withAxiom(x315);

		Term x318 = Term.mkApp("TO/Ord.Next", x8, x20, x17);
		Term x317 = Term.mkNot(x318);
		theory = theory.withAxiom(x317);

		Term x320 = Term.mkApp("TO/Ord.Next", x8, x44, x66);
		Term x319 = Term.mkNot(x320);
		theory = theory.withAxiom(x319);

		Term x322 = Term.mkApp("TO/Ord.Next", x8, x26, x26);
		Term x321 = Term.mkNot(x322);
		theory = theory.withAxiom(x321);

		Term x324 = Term.mkApp("TO/Ord.Next", x8, x9, x9);
		Term x323 = Term.mkNot(x324);
		theory = theory.withAxiom(x323);

		Term x326 = Term.mkApp("TO/Ord.Next", x8, x32, x26);
		Term x325 = Term.mkNot(x326);
		theory = theory.withAxiom(x325);

		Term x328 = Term.mkApp("TO/Ord.Next", x8, x17, x66);
		Term x327 = Term.mkNot(x328);
		theory = theory.withAxiom(x327);

		Term x330 = Term.mkApp("TO/Ord.Next", x8, x29, x66);
		Term x329 = Term.mkNot(x330);
		theory = theory.withAxiom(x329);

		Var x332 = Term.mkVar("var_1");
		Var x333 = Term.mkVar("var_2");
		Var x334 = Term.mkVar("var_3");
		Var x335 = Term.mkVar("var_4");
		Var x336 = Term.mkVar("var_5");
		Var x337 = Term.mkVar("var_6");
		Var x338 = Term.mkVar("var_7");
		Var x339 = Term.mkVar("var_8");
		Var x340 = Term.mkVar("var_9");
		Var x341 = Term.mkVar("var_10");
		Var x342 = Term.mkVar("var_11");
		Var x343 = Term.mkVar("var_12");
		Var x344 = Term.mkVar("var_13");
		Term x346 = Term.mkApp("this/Time", x332);
		Term x348 = Term.mkEq(x333, x332);
		Term x347 = Term.mkNot(x348);
		Term x349 = Term.mkApp("this/Time", x333);
		Term x351 = Term.mkEq(x334, x332);
		Term x350 = Term.mkNot(x351);
		Term x353 = Term.mkEq(x334, x333);
		Term x352 = Term.mkNot(x353);
		Term x354 = Term.mkApp("this/Time", x334);
		Term x356 = Term.mkEq(x335, x332);
		Term x355 = Term.mkNot(x356);
		Term x358 = Term.mkEq(x335, x333);
		Term x357 = Term.mkNot(x358);
		Term x360 = Term.mkEq(x335, x334);
		Term x359 = Term.mkNot(x360);
		Term x361 = Term.mkApp("this/Time", x335);
		Term x363 = Term.mkEq(x336, x332);
		Term x362 = Term.mkNot(x363);
		Term x365 = Term.mkEq(x336, x333);
		Term x364 = Term.mkNot(x365);
		Term x367 = Term.mkEq(x336, x334);
		Term x366 = Term.mkNot(x367);
		Term x369 = Term.mkEq(x336, x335);
		Term x368 = Term.mkNot(x369);
		Term x370 = Term.mkApp("this/Time", x336);
		Term x372 = Term.mkEq(x337, x332);
		Term x371 = Term.mkNot(x372);
		Term x374 = Term.mkEq(x337, x333);
		Term x373 = Term.mkNot(x374);
		Term x376 = Term.mkEq(x337, x334);
		Term x375 = Term.mkNot(x376);
		Term x378 = Term.mkEq(x337, x335);
		Term x377 = Term.mkNot(x378);
		Term x380 = Term.mkEq(x337, x336);
		Term x379 = Term.mkNot(x380);
		Term x381 = Term.mkApp("this/Time", x337);
		Term x383 = Term.mkEq(x338, x332);
		Term x382 = Term.mkNot(x383);
		Term x385 = Term.mkEq(x338, x333);
		Term x384 = Term.mkNot(x385);
		Term x387 = Term.mkEq(x338, x334);
		Term x386 = Term.mkNot(x387);
		Term x389 = Term.mkEq(x338, x335);
		Term x388 = Term.mkNot(x389);
		Term x391 = Term.mkEq(x338, x336);
		Term x390 = Term.mkNot(x391);
		Term x393 = Term.mkEq(x338, x337);
		Term x392 = Term.mkNot(x393);
		Term x394 = Term.mkApp("this/Time", x338);
		Term x396 = Term.mkEq(x339, x332);
		Term x395 = Term.mkNot(x396);
		Term x398 = Term.mkEq(x339, x333);
		Term x397 = Term.mkNot(x398);
		Term x400 = Term.mkEq(x339, x334);
		Term x399 = Term.mkNot(x400);
		Term x402 = Term.mkEq(x339, x335);
		Term x401 = Term.mkNot(x402);
		Term x404 = Term.mkEq(x339, x336);
		Term x403 = Term.mkNot(x404);
		Term x406 = Term.mkEq(x339, x337);
		Term x405 = Term.mkNot(x406);
		Term x408 = Term.mkEq(x339, x338);
		Term x407 = Term.mkNot(x408);
		Term x409 = Term.mkApp("this/Time", x339);
		Term x411 = Term.mkEq(x340, x332);
		Term x410 = Term.mkNot(x411);
		Term x413 = Term.mkEq(x340, x333);
		Term x412 = Term.mkNot(x413);
		Term x415 = Term.mkEq(x340, x334);
		Term x414 = Term.mkNot(x415);
		Term x417 = Term.mkEq(x340, x335);
		Term x416 = Term.mkNot(x417);
		Term x419 = Term.mkEq(x340, x336);
		Term x418 = Term.mkNot(x419);
		Term x421 = Term.mkEq(x340, x337);
		Term x420 = Term.mkNot(x421);
		Term x423 = Term.mkEq(x340, x338);
		Term x422 = Term.mkNot(x423);
		Term x425 = Term.mkEq(x340, x339);
		Term x424 = Term.mkNot(x425);
		Term x426 = Term.mkApp("this/Time", x340);
		Term x428 = Term.mkEq(x341, x332);
		Term x427 = Term.mkNot(x428);
		Term x430 = Term.mkEq(x341, x333);
		Term x429 = Term.mkNot(x430);
		Term x432 = Term.mkEq(x341, x334);
		Term x431 = Term.mkNot(x432);
		Term x434 = Term.mkEq(x341, x335);
		Term x433 = Term.mkNot(x434);
		Term x436 = Term.mkEq(x341, x336);
		Term x435 = Term.mkNot(x436);
		Term x438 = Term.mkEq(x341, x337);
		Term x437 = Term.mkNot(x438);
		Term x440 = Term.mkEq(x341, x338);
		Term x439 = Term.mkNot(x440);
		Term x442 = Term.mkEq(x341, x339);
		Term x441 = Term.mkNot(x442);
		Term x444 = Term.mkEq(x341, x340);
		Term x443 = Term.mkNot(x444);
		Term x445 = Term.mkApp("this/Time", x341);
		Term x447 = Term.mkEq(x342, x332);
		Term x446 = Term.mkNot(x447);
		Term x449 = Term.mkEq(x342, x333);
		Term x448 = Term.mkNot(x449);
		Term x451 = Term.mkEq(x342, x334);
		Term x450 = Term.mkNot(x451);
		Term x453 = Term.mkEq(x342, x335);
		Term x452 = Term.mkNot(x453);
		Term x455 = Term.mkEq(x342, x336);
		Term x454 = Term.mkNot(x455);
		Term x457 = Term.mkEq(x342, x337);
		Term x456 = Term.mkNot(x457);
		Term x459 = Term.mkEq(x342, x338);
		Term x458 = Term.mkNot(x459);
		Term x461 = Term.mkEq(x342, x339);
		Term x460 = Term.mkNot(x461);
		Term x463 = Term.mkEq(x342, x340);
		Term x462 = Term.mkNot(x463);
		Term x465 = Term.mkEq(x342, x341);
		Term x464 = Term.mkNot(x465);
		Term x466 = Term.mkApp("this/Time", x342);
		Term x468 = Term.mkEq(x343, x332);
		Term x467 = Term.mkNot(x468);
		Term x470 = Term.mkEq(x343, x333);
		Term x469 = Term.mkNot(x470);
		Term x472 = Term.mkEq(x343, x334);
		Term x471 = Term.mkNot(x472);
		Term x474 = Term.mkEq(x343, x335);
		Term x473 = Term.mkNot(x474);
		Term x476 = Term.mkEq(x343, x336);
		Term x475 = Term.mkNot(x476);
		Term x478 = Term.mkEq(x343, x337);
		Term x477 = Term.mkNot(x478);
		Term x480 = Term.mkEq(x343, x338);
		Term x479 = Term.mkNot(x480);
		Term x482 = Term.mkEq(x343, x339);
		Term x481 = Term.mkNot(x482);
		Term x484 = Term.mkEq(x343, x340);
		Term x483 = Term.mkNot(x484);
		Term x486 = Term.mkEq(x343, x341);
		Term x485 = Term.mkNot(x486);
		Term x488 = Term.mkEq(x343, x342);
		Term x487 = Term.mkNot(x488);
		Term x489 = Term.mkApp("this/Time", x343);
		Term x491 = Term.mkEq(x344, x332);
		Term x490 = Term.mkNot(x491);
		Term x493 = Term.mkEq(x344, x333);
		Term x492 = Term.mkNot(x493);
		Term x495 = Term.mkEq(x344, x334);
		Term x494 = Term.mkNot(x495);
		Term x497 = Term.mkEq(x344, x335);
		Term x496 = Term.mkNot(x497);
		Term x499 = Term.mkEq(x344, x336);
		Term x498 = Term.mkNot(x499);
		Term x501 = Term.mkEq(x344, x337);
		Term x500 = Term.mkNot(x501);
		Term x503 = Term.mkEq(x344, x338);
		Term x502 = Term.mkNot(x503);
		Term x505 = Term.mkEq(x344, x339);
		Term x504 = Term.mkNot(x505);
		Term x507 = Term.mkEq(x344, x340);
		Term x506 = Term.mkNot(x507);
		Term x509 = Term.mkEq(x344, x341);
		Term x508 = Term.mkNot(x509);
		Term x511 = Term.mkEq(x344, x342);
		Term x510 = Term.mkNot(x511);
		Term x513 = Term.mkEq(x344, x343);
		Term x512 = Term.mkNot(x513);
		Term x514 = Term.mkApp("this/Time", x344);
		Var x516 = Term.mkVar("var_14");
		Term x518 = Term.mkApp("this/Time", x516);
		Term x520 = Term.mkEq(x516, x332);
		Term x521 = Term.mkEq(x516, x333);
		Term x522 = Term.mkEq(x516, x334);
		Term x523 = Term.mkEq(x516, x335);
		Term x524 = Term.mkEq(x516, x336);
		Term x525 = Term.mkEq(x516, x337);
		Term x526 = Term.mkEq(x516, x338);
		Term x527 = Term.mkEq(x516, x339);
		Term x528 = Term.mkEq(x516, x340);
		Term x529 = Term.mkEq(x516, x341);
		Term x530 = Term.mkEq(x516, x342);
		Term x531 = Term.mkEq(x516, x343);
		Term x532 = Term.mkEq(x516, x344);
		Term x519 = Term.mkOr(x520, x521, x522, x523, x524, x525, x526, x527, x528, x529, x530, x531, x532);
		Term x517 = Term.mkImp(x518, x519);
		Term x515 = Term.mkForall(List.of(x516.of(x2)), x517);
		Term x345 = Term.mkAnd(x346, x347, x349, x350, x352, x354, x355, x357, x359, x361, x362, x364, x366, x368, x370, x371, x373, x375, x377, x379, x381, x382, x384, x386, x388, x390, x392, x394, x395, x397, x399, x401, x403, x405, x407, x409, x410, x412, x414, x416, x418, x420, x422, x424, x426, x427, x429, x431, x433, x435, x437, x439, x441, x443, x445, x446, x448, x450, x452, x454, x456, x458, x460, x462, x464, x466, x467, x469, x471, x473, x475, x477, x479, x481, x483, x485, x487, x489, x490, x492, x494, x496, x498, x500, x502, x504, x506, x508, x510, x512, x514, x515);
		Term x331 = Term.mkExists(List.of(x332.of(x2), x333.of(x2), x334.of(x2), x335.of(x2), x336.of(x2), x337.of(x2), x338.of(x2), x339.of(x2), x340.of(x2), x341.of(x2), x342.of(x2), x343.of(x2), x344.of(x2)), x345);
		theory = theory.withAxiom(x331);

		Term x534 = Term.mkApp("TO/Ord.Next", x8, x39, x39);
		Term x533 = Term.mkNot(x534);
		theory = theory.withAxiom(x533);

		Term x536 = Term.mkApp("TO/Ord.First", x8, x32);
		Term x535 = Term.mkNot(x536);
		theory = theory.withAxiom(x535);

		Term x538 = Term.mkApp("TO/Ord.Next", x8, x47, x44);
		Term x537 = Term.mkNot(x538);
		theory = theory.withAxiom(x537);

		Term x540 = Term.mkApp("TO/Ord.Next", x8, x29, x29);
		Term x539 = Term.mkNot(x540);
		theory = theory.withAxiom(x539);

		Term x542 = Term.mkApp("TO/Ord.Next", x8, x17, x29);
		Term x541 = Term.mkNot(x542);
		theory = theory.withAxiom(x541);

		Term x544 = Term.mkApp("TO/Ord.Next", x8, x44, x9);
		Term x543 = Term.mkNot(x544);
		theory = theory.withAxiom(x543);

		Term x546 = Term.mkApp("TO/Ord.Next", x8, x47, x39);
		Term x545 = Term.mkNot(x546);
		theory = theory.withAxiom(x545);

		Term x548 = Term.mkApp("TO/Ord.Next", x8, x47, x66);
		Term x547 = Term.mkNot(x548);
		theory = theory.withAxiom(x547);

		Term x550 = Term.mkApp("TO/Ord.Next", x8, x32, x9);
		Term x549 = Term.mkNot(x550);
		theory = theory.withAxiom(x549);

		Term x552 = Term.mkApp("TO/Ord.Next", x8, x80, x32);
		Term x551 = Term.mkNot(x552);
		theory = theory.withAxiom(x551);

		Var x554 = Term.mkVar("looplessPath_this_2");
		Term x556 = Term.mkApp("this/Process", x554);
		Var x558 = Term.mkVar("var_48");
		Term x560 = Term.mkApp("this/Process.elected", x554, x558);
		Term x561 = Term.mkApp("this/Time", x558);
		Term x559 = Term.mkImp(x560, x561);
		Term x557 = Term.mkForall(List.of(x558.of(x2)), x559);
		Term x555 = Term.mkImp(x556, x557);
		Term x553 = Term.mkForall(List.of(x554.of(x3)), x555);
		theory = theory.withAxiom(x553);

		Term x563 = Term.mkApp("TO/Ord.Next", x8, x32, x44);
		Term x562 = Term.mkNot(x563);
		theory = theory.withAxiom(x562);

		Term x565 = Term.mkApp("PO/Ord.Next", x11, x23, x12);
		Term x564 = Term.mkNot(x565);
		theory = theory.withAxiom(x564);

		Term x567 = Term.mkApp("TO/Ord.Next", x8, x26, x16);
		Term x566 = Term.mkNot(x567);
		theory = theory.withAxiom(x566);

		Term x569 = Term.mkApp("TO/Ord.Next", x8, x32, x39);
		Term x568 = Term.mkNot(x569);
		theory = theory.withAxiom(x568);

		Term x571 = Term.mkApp("TO/Ord.First", x8, x44);
		Term x570 = Term.mkNot(x571);
		theory = theory.withAxiom(x570);

		Term x573 = Term.mkApp("TO/Ord.Next", x8, x26, x80);
		Term x572 = Term.mkNot(x573);
		theory = theory.withAxiom(x572);

		Term x575 = Term.mkApp("TO/Ord.Next", x8, x66, x32);
		Term x574 = Term.mkNot(x575);
		theory = theory.withAxiom(x574);

		Var x577 = Term.mkVar("var_33");
		Var x578 = Term.mkVar("var_34");
		Term x580 = Term.mkApp("TO/Ord.First", x577, x578);
		Term x582 = Term.mkApp("TO/Ord", x577);
		Term x583 = Term.mkApp("this/Time", x578);
		Term x581 = Term.mkAnd(x582, x583);
		Term x579 = Term.mkImp(x580, x581);
		Term x576 = Term.mkForall(List.of(x577.of(x4), x578.of(x2)), x579);
		theory = theory.withAxiom(x576);

		Term x585 = Term.mkApp("TO/Ord.Next", x8, x21, x39);
		Term x584 = Term.mkNot(x585);
		theory = theory.withAxiom(x584);

		Term x587 = Term.mkApp("TO/Ord.Next", x8, x17, x47);
		Term x586 = Term.mkNot(x587);
		theory = theory.withAxiom(x586);

		Term x589 = Term.mkApp("TO/Ord.Next", x8, x66, x21);
		Term x588 = Term.mkNot(x589);
		theory = theory.withAxiom(x588);

		Term x591 = Term.mkApp("TO/Ord.Next", x8, x39, x32);
		Term x590 = Term.mkNot(x591);
		theory = theory.withAxiom(x590);

		Var x593 = Term.mkVar("var_40");
		Var x594 = Term.mkVar("var_41");
		Var x595 = Term.mkVar("var_42");
		Term x597 = Term.mkApp("PO/Ord.Next", x593, x594, x595);
		Term x600 = Term.mkApp("PO/Ord", x593);
		Term x601 = Term.mkApp("this/Process", x594);
		Term x599 = Term.mkAnd(x600, x601);
		Term x602 = Term.mkApp("this/Process", x595);
		Term x598 = Term.mkAnd(x599, x602);
		Term x596 = Term.mkImp(x597, x598);
		Term x592 = Term.mkForall(List.of(x593.of(x5), x594.of(x3), x595.of(x3)), x596);
		theory = theory.withAxiom(x592);

		Term x604 = Term.mkApp("TO/Ord.Next", x8, x47, x9);
		Term x603 = Term.mkNot(x604);
		theory = theory.withAxiom(x603);

		Term x605 = Term.mkApp("TO/Ord.First", x8, x80);
		theory = theory.withAxiom(x605);

		Term x607 = Term.mkApp("TO/Ord.Next", x8, x20, x80);
		Term x606 = Term.mkNot(x607);
		theory = theory.withAxiom(x606);

		Term x609 = Term.mkApp("TO/Ord.Next", x8, x9, x47);
		Term x608 = Term.mkNot(x609);
		theory = theory.withAxiom(x608);

		Term x611 = Term.mkApp("TO/Ord.Next", x8, x47, x26);
		Term x610 = Term.mkNot(x611);
		theory = theory.withAxiom(x610);

		Term x612 = Term.mkApp("TO/Ord.Next", x8, x29, x47);
		theory = theory.withAxiom(x612);

		Term x614 = Term.mkApp("TO/Ord.Next", x8, x32, x20);
		Term x613 = Term.mkNot(x614);
		theory = theory.withAxiom(x613);

		Term x616 = Term.mkApp("TO/Ord.Next", x8, x16, x21);
		Term x615 = Term.mkNot(x616);
		theory = theory.withAxiom(x615);

		Term x618 = Term.mkApp("TO/Ord.Next", x8, x20, x39);
		Term x617 = Term.mkNot(x618);
		theory = theory.withAxiom(x617);

		Term x620 = Term.mkApp("TO/Ord.Next", x8, x29, x44);
		Term x619 = Term.mkNot(x620);
		theory = theory.withAxiom(x619);

		Term x622 = Term.mkApp("TO/Ord.First", x8, x16);
		Term x621 = Term.mkNot(x622);
		theory = theory.withAxiom(x621);

		Term x624 = Term.mkApp("TO/Ord.Next", x8, x20, x9);
		Term x623 = Term.mkNot(x624);
		theory = theory.withAxiom(x623);

		Term x626 = Term.mkApp("TO/Ord.Next", x8, x17, x17);
		Term x625 = Term.mkNot(x626);
		theory = theory.withAxiom(x625);

		Term x628 = Term.mkApp("TO/Ord.Next", x8, x21, x47);
		Term x627 = Term.mkNot(x628);
		theory = theory.withAxiom(x627);

		Term x630 = Term.mkApp("TO/Ord.Next", x8, x21, x32);
		Term x629 = Term.mkNot(x630);
		theory = theory.withAxiom(x629);

		Term x632 = Term.mkApp("TO/Ord.Next", x8, x20, x29);
		Term x631 = Term.mkNot(x632);
		theory = theory.withAxiom(x631);

		Term x634 = Term.mkApp("TO/Ord.Next", x8, x21, x16);
		Term x633 = Term.mkNot(x634);
		theory = theory.withAxiom(x633);

		Var x636 = Term.mkVar("var_60");
		Var x639 = Term.mkVar("var_61");
		Term x641 = Term.mkApp("this/Process.elected", x636, x639);
		Var x643 = Term.mkVar("var_62");
		Term x645 = Term.mkApp("TO/Ord", x643);
		Term x646 = Term.mkApp("TO/Ord.First", x643, x639);
		Term x644 = Term.mkAnd(x645, x646);
		Term x642 = Term.mkExists(List.of(x643.of(x4)), x644);
		Term x640 = Term.mkAnd(x641, x642);
		Term x638 = Term.mkExists(List.of(x639.of(x2)), x640);
		Term x637 = Term.mkNot(x638);
		Term x635 = Term.mkForall(List.of(x636.of(x3)), x637);
		theory = theory.withAxiom(x635);

		Term x648 = Term.mkApp("TO/Ord.Next", x8, x80, x17);
		Term x647 = Term.mkNot(x648);
		theory = theory.withAxiom(x647);

		Term x650 = Term.mkApp("TO/Ord.Next", x8, x21, x29);
		Term x649 = Term.mkNot(x650);
		theory = theory.withAxiom(x649);

		Term x652 = Term.mkApp("TO/Ord.Next", x8, x44, x39);
		Term x651 = Term.mkNot(x652);
		theory = theory.withAxiom(x651);

		Term x654 = Term.mkApp("TO/Ord.Next", x8, x66, x39);
		Term x653 = Term.mkNot(x654);
		theory = theory.withAxiom(x653);

		Term x656 = Term.mkApp("TO/Ord.Next", x8, x32, x29);
		Term x655 = Term.mkNot(x656);
		theory = theory.withAxiom(x655);

		Term x658 = Term.mkApp("TO/Ord.Next", x8, x66, x20);
		Term x657 = Term.mkNot(x658);
		theory = theory.withAxiom(x657);

		Term x660 = Term.mkApp("TO/Ord.Next", x8, x80, x16);
		Term x659 = Term.mkNot(x660);
		theory = theory.withAxiom(x659);

		Term x662 = Term.mkApp("TO/Ord.Next", x8, x44, x32);
		Term x661 = Term.mkNot(x662);
		theory = theory.withAxiom(x661);

		Term x664 = Term.mkApp("TO/Ord.Next", x8, x21, x20);
		Term x663 = Term.mkNot(x664);
		theory = theory.withAxiom(x663);

		Term x666 = Term.mkApp("PO/Ord.Next", x11, x13, x12);
		Term x665 = Term.mkNot(x666);
		theory = theory.withAxiom(x665);

		Term x668 = Term.mkApp("TO/Ord.Next", x8, x44, x16);
		Term x667 = Term.mkNot(x668);
		theory = theory.withAxiom(x667);

		Term x670 = Term.mkApp("TO/Ord.First", x8, x47);
		Term x669 = Term.mkNot(x670);
		theory = theory.withAxiom(x669);

		Term x671 = Term.mkApp("PO/Ord.First", x11, x12);
		theory = theory.withAxiom(x671);

		Term x673 = Term.mkApp("PO/Ord.Next", x11, x13, x13);
		Term x672 = Term.mkNot(x673);
		theory = theory.withAxiom(x672);

		Term x674 = Term.mkApp("TO/Ord.Next", x8, x20, x16);
		theory = theory.withAxiom(x674);

		Term x676 = Term.mkApp("TO/Ord.Next", x8, x80, x20);
		Term x675 = Term.mkNot(x676);
		theory = theory.withAxiom(x675);

		Var x678 = Term.mkVar("var_38");
		Var x679 = Term.mkVar("var_39");
		Term x681 = Term.mkApp("PO/Ord.First", x678, x679);
		Term x683 = Term.mkApp("PO/Ord", x678);
		Term x684 = Term.mkApp("this/Process", x679);
		Term x682 = Term.mkAnd(x683, x684);
		Term x680 = Term.mkImp(x681, x682);
		Term x677 = Term.mkForall(List.of(x678.of(x5), x679.of(x3)), x680);
		theory = theory.withAxiom(x677);

		Term x686 = Term.mkApp("TO/Ord.Next", x8, x21, x17);
		Term x685 = Term.mkNot(x686);
		theory = theory.withAxiom(x685);

		Term x688 = Term.mkApp("TO/Ord.Next", x8, x66, x17);
		Term x687 = Term.mkNot(x688);
		theory = theory.withAxiom(x687);

		Var x690 = Term.mkVar("looplessPath_t_2");
		Var x691 = Term.mkVar("looplessPath_t'_0");
		Term x694 = Term.mkApp("this/Time", x690);
		Term x695 = Term.mkApp("this/Time", x691);
		Term x693 = Term.mkAnd(x694, x695);
		Term x698 = Term.mkDistinct(x690, x691);
		Var x700 = Term.mkVar("var_112");
		Var x701 = Term.mkVar("var_113");
		Term x703 = Term.mkApp("this/Process.toSend", x700, x701, x690);
		Term x704 = Term.mkApp("this/Process.toSend", x700, x701, x691);
		Term x702 = Term.mkIff(x703, x704);
		Term x699 = Term.mkForall(List.of(x700.of(x3), x701.of(x3)), x702);
		Term x697 = Term.mkAnd(x698, x699);
		Term x696 = Term.mkNot(x697);
		Term x692 = Term.mkImp(x693, x696);
		Term x689 = Term.mkForall(List.of(x690.of(x2), x691.of(x2)), x692);
		theory = theory.withAxiom(x689);

		Var x706 = Term.mkVar("looplessPath_this_1");
		Term x708 = Term.mkApp("this/Process", x706);
		Var x710 = Term.mkVar("var_46");
		Var x711 = Term.mkVar("var_47");
		Term x713 = Term.mkApp("this/Process.toSend", x706, x710, x711);
		Term x715 = Term.mkApp("this/Process", x710);
		Term x716 = Term.mkApp("this/Time", x711);
		Term x714 = Term.mkAnd(x715, x716);
		Term x712 = Term.mkImp(x713, x714);
		Term x709 = Term.mkForall(List.of(x710.of(x3), x711.of(x2)), x712);
		Term x707 = Term.mkImp(x708, x709);
		Term x705 = Term.mkForall(List.of(x706.of(x3)), x707);
		theory = theory.withAxiom(x705);

		Term x718 = Term.mkApp("PO/Ord.Next", x11, x12, x12);
		Term x717 = Term.mkNot(x718);
		theory = theory.withAxiom(x717);

		Term x720 = Term.mkApp("TO/Ord.Next", x8, x17, x44);
		Term x719 = Term.mkNot(x720);
		theory = theory.withAxiom(x719);

		Term x722 = Term.mkApp("TO/Ord.Next", x8, x44, x44);
		Term x721 = Term.mkNot(x722);
		theory = theory.withAxiom(x721);

		Var x724 = Term.mkVar("var_54");
		Var x727 = Term.mkVar("var_55");
		Term x729 = Term.mkApp("PO/Ord", x727);
		Term x730 = Term.mkApp("PO/Ord.First", x727, x724);
		Term x728 = Term.mkAnd(x729, x730);
		Term x726 = Term.mkExists(List.of(x727.of(x5)), x728);
		Term x731 = Term.mkApp("this/Process", x724);
		Term x725 = Term.mkImp(x726, x731);
		Term x723 = Term.mkForall(List.of(x724.of(x3)), x725);
		theory = theory.withAxiom(x723);

		Term x733 = Term.mkApp("TO/Ord.First", x8, x29);
		Term x732 = Term.mkNot(x733);
		theory = theory.withAxiom(x732);

		Term x735 = Term.mkApp("TO/Ord.Next", x8, x80, x21);
		Term x734 = Term.mkNot(x735);
		theory = theory.withAxiom(x734);

		Term x737 = Term.mkApp("TO/Ord.Next", x8, x80, x47);
		Term x736 = Term.mkNot(x737);
		theory = theory.withAxiom(x736);

		Term x739 = Term.mkApp("TO/Ord.Next", x8, x9, x17);
		Term x738 = Term.mkNot(x739);
		theory = theory.withAxiom(x738);

		Term x741 = Term.mkApp("TO/Ord.Next", x8, x32, x80);
		Term x740 = Term.mkNot(x741);
		theory = theory.withAxiom(x740);

		Term x743 = Term.mkApp("TO/Ord.Next", x8, x66, x47);
		Term x742 = Term.mkNot(x743);
		theory = theory.withAxiom(x742);

		Term x745 = Term.mkApp("TO/Ord.Next", x8, x16, x26);
		Term x744 = Term.mkNot(x745);
		theory = theory.withAxiom(x744);

		Term x747 = Term.mkApp("TO/Ord.Next", x8, x21, x21);
		Term x746 = Term.mkNot(x747);
		theory = theory.withAxiom(x746);

		Term x748 = Term.mkApp("TO/Ord.Next", x8, x9, x32);
		theory = theory.withAxiom(x748);

		Var x750 = Term.mkVar("var_21");
		Term x752 = Term.mkApp("TO/Ord", x750);
		Var x754 = Term.mkVar("var_22");
		Term x756 = Term.mkApp("TO/Ord", x754);
		Term x757 = Term.mkEq(x754, x750);
		Term x755 = Term.mkImp(x756, x757);
		Term x753 = Term.mkForall(List.of(x754.of(x4)), x755);
		Term x751 = Term.mkAnd(x752, x753);
		Term x749 = Term.mkExists(List.of(x750.of(x4)), x751);
		theory = theory.withAxiom(x749);

		Term x759 = Term.mkApp("TO/Ord.Next", x8, x47, x32);
		Term x758 = Term.mkNot(x759);
		theory = theory.withAxiom(x758);

		Term x761 = Term.mkApp("TO/Ord.Next", x8, x47, x47);
		Term x760 = Term.mkNot(x761);
		theory = theory.withAxiom(x760);

		Term x763 = Term.mkApp("TO/Ord.Next", x8, x39, x16);
		Term x762 = Term.mkNot(x763);
		theory = theory.withAxiom(x762);

		Var x765 = Term.mkVar("var_16");
		Var x766 = Term.mkVar("var_17");
		Var x767 = Term.mkVar("var_18");
		Term x769 = Term.mkApp("this/Process", x765);
		Term x771 = Term.mkEq(x766, x765);
		Term x770 = Term.mkNot(x771);
		Term x772 = Term.mkApp("this/Process", x766);
		Term x774 = Term.mkEq(x767, x765);
		Term x773 = Term.mkNot(x774);
		Term x776 = Term.mkEq(x767, x766);
		Term x775 = Term.mkNot(x776);
		Term x777 = Term.mkApp("this/Process", x767);
		Var x779 = Term.mkVar("var_19");
		Term x781 = Term.mkApp("this/Process", x779);
		Term x783 = Term.mkEq(x779, x765);
		Term x784 = Term.mkEq(x779, x766);
		Term x785 = Term.mkEq(x779, x767);
		Term x782 = Term.mkOr(x783, x784, x785);
		Term x780 = Term.mkImp(x781, x782);
		Term x778 = Term.mkForall(List.of(x779.of(x3)), x780);
		Term x768 = Term.mkAnd(x769, x770, x772, x773, x775, x777, x778);
		Term x764 = Term.mkExists(List.of(x765.of(x3), x766.of(x3), x767.of(x3)), x768);
		theory = theory.withAxiom(x764);

		Term x787 = Term.mkApp("TO/Ord.Next", x8, x26, x29);
		Term x786 = Term.mkNot(x787);
		theory = theory.withAxiom(x786);

		Term x789 = Term.mkApp("PO/Ord.Next", x11, x23, x23);
		Term x788 = Term.mkNot(x789);
		theory = theory.withAxiom(x788);

		Term x791 = Term.mkApp("TO/Ord.Next", x8, x47, x21);
		Term x790 = Term.mkNot(x791);
		theory = theory.withAxiom(x790);

		Var x793 = Term.mkVar("var_24");
		Term x795 = Term.mkApp("PO/Ord", x793);
		Var x797 = Term.mkVar("var_25");
		Term x799 = Term.mkApp("PO/Ord", x797);
		Term x800 = Term.mkEq(x797, x793);
		Term x798 = Term.mkImp(x799, x800);
		Term x796 = Term.mkForall(List.of(x797.of(x5)), x798);
		Term x794 = Term.mkAnd(x795, x796);
		Term x792 = Term.mkExists(List.of(x793.of(x5)), x794);
		theory = theory.withAxiom(x792);

		Term x801 = Term.mkApp("TO/Ord.Next", x8, x17, x20);
		theory = theory.withAxiom(x801);

		Term x803 = Term.mkApp("TO/Ord.Next", x8, x20, x44);
		Term x802 = Term.mkNot(x803);
		theory = theory.withAxiom(x802);

		Term x805 = Term.mkApp("TO/Ord.Next", x8, x47, x29);
		Term x804 = Term.mkNot(x805);
		theory = theory.withAxiom(x804);

		Term x807 = Term.mkApp("TO/Ord.Next", x8, x39, x47);
		Term x806 = Term.mkNot(x807);
		theory = theory.withAxiom(x806);

		Term x808 = Term.mkApp("TO/Ord.Next", x8, x39, x17);
		theory = theory.withAxiom(x808);

		Term x810 = Term.mkApp("TO/Ord.Next", x8, x20, x20);
		Term x809 = Term.mkNot(x810);
		theory = theory.withAxiom(x809);

		Term x812 = Term.mkApp("TO/Ord.Next", x8, x26, x32);
		Term x811 = Term.mkNot(x812);
		theory = theory.withAxiom(x811);

		Var x814 = Term.mkVar("var_35");
		Var x815 = Term.mkVar("var_36");
		Var x816 = Term.mkVar("var_37");
		Term x818 = Term.mkApp("TO/Ord.Next", x814, x815, x816);
		Term x821 = Term.mkApp("TO/Ord", x814);
		Term x822 = Term.mkApp("this/Time", x815);
		Term x820 = Term.mkAnd(x821, x822);
		Term x823 = Term.mkApp("this/Time", x816);
		Term x819 = Term.mkAnd(x820, x823);
		Term x817 = Term.mkImp(x818, x819);
		Term x813 = Term.mkForall(List.of(x814.of(x4), x815.of(x2), x816.of(x2)), x817);
		theory = theory.withAxiom(x813);

		Term x825 = Term.mkApp("TO/Ord.Next", x8, x16, x32);
		Term x824 = Term.mkNot(x825);
		theory = theory.withAxiom(x824);

		Term x827 = Term.mkApp("TO/Ord.Next", x8, x29, x17);
		Term x826 = Term.mkNot(x827);
		theory = theory.withAxiom(x826);

		Term x829 = Term.mkApp("TO/Ord.Next", x8, x29, x80);
		Term x828 = Term.mkNot(x829);
		theory = theory.withAxiom(x828);

		Term x831 = Term.mkApp("PO/Ord.Next", x11, x23, x13);
		Term x830 = Term.mkNot(x831);
		theory = theory.withAxiom(x830);

		Term x833 = Term.mkApp("TO/Ord.Next", x8, x9, x21);
		Term x832 = Term.mkNot(x833);
		theory = theory.withAxiom(x832);

		Term x835 = Term.mkApp("TO/Ord.Next", x8, x39, x80);
		Term x834 = Term.mkNot(x835);
		theory = theory.withAxiom(x834);

		Term x836 = Term.mkApp("TO/Ord.Next", x8, x26, x9);
		theory = theory.withAxiom(x836);

		Term x838 = Term.mkApp("TO/Ord.Next", x8, x9, x20);
		Term x837 = Term.mkNot(x838);
		theory = theory.withAxiom(x837);

		Term x840 = Term.mkApp("TO/Ord.Next", x8, x39, x29);
		Term x839 = Term.mkNot(x840);
		theory = theory.withAxiom(x839);

		Term x842 = Term.mkApp("TO/Ord.Next", x8, x9, x66);
		Term x841 = Term.mkNot(x842);
		theory = theory.withAxiom(x841);

		Term x844 = Term.mkApp("TO/Ord.Next", x8, x80, x29);
		Term x843 = Term.mkNot(x844);
		theory = theory.withAxiom(x843);

		Term x846 = Term.mkApp("TO/Ord.Next", x8, x21, x9);
		Term x845 = Term.mkNot(x846);
		theory = theory.withAxiom(x845);

		Term x848 = Term.mkApp("TO/Ord.Next", x8, x29, x32);
		Term x847 = Term.mkNot(x848);
		theory = theory.withAxiom(x847);

		Term x850 = Term.mkApp("TO/Ord.Next", x8, x17, x21);
		Term x849 = Term.mkNot(x850);
		theory = theory.withAxiom(x849);

		Term x851 = Term.mkApp("TO/Ord.Next", x8, x21, x26);
		theory = theory.withAxiom(x851);

		Term x853 = Term.mkApp("TO/Ord.Next", x8, x44, x80);
		Term x852 = Term.mkNot(x853);
		theory = theory.withAxiom(x852);

		Term x855 = Term.mkApp("TO/Ord.Next", x8, x44, x29);
		Term x854 = Term.mkNot(x855);
		theory = theory.withAxiom(x854);

		Term x857 = Term.mkApp("TO/Ord.Next", x8, x80, x26);
		Term x856 = Term.mkNot(x857);
		theory = theory.withAxiom(x856);

		Term x859 = Term.mkApp("TO/Ord.Next", x8, x16, x9);
		Term x858 = Term.mkNot(x859);
		theory = theory.withAxiom(x858);

		Term x861 = Term.mkApp("TO/Ord.Next", x8, x20, x32);
		Term x860 = Term.mkNot(x861);
		theory = theory.withAxiom(x860);

		Term x862 = Term.mkApp("TO/Ord.Next", x8, x16, x44);
		theory = theory.withAxiom(x862);

		Term x864 = Term.mkApp("PO/Ord.Next", x11, x12, x23);
		Term x863 = Term.mkNot(x864);
		theory = theory.withAxiom(x863);

		Var x866 = Term.mkVar("var_86");
		Var x867 = Term.mkVar("var_87");
		Term x869 = Term.mkApp("func_1", x866, x867);
		Var x871 = Term.mkVar("var_88");
		Term x873 = Term.mkApp("PO/Ord", x871);
		Term x874 = Term.mkApp("PO/Ord.Next", x871, x867, x866);
		Term x872 = Term.mkAnd(x873, x874);
		Term x870 = Term.mkExists(List.of(x871.of(x5)), x872);
		Term x868 = Term.mkIff(x869, x870);
		Term x865 = Term.mkForall(List.of(x866.of(x3), x867.of(x3)), x868);
		theory = theory.withAxiom(x865);

		Term x876 = Term.mkApp("TO/Ord.Next", x8, x47, x20);
		Term x875 = Term.mkNot(x876);
		theory = theory.withAxiom(x875);

		Term x878 = Term.mkApp("TO/Ord.Next", x8, x66, x66);
		Term x877 = Term.mkNot(x878);
		theory = theory.withAxiom(x877);

		Term x880 = Term.mkApp("TO/Ord.First", x8, x66);
		Term x879 = Term.mkNot(x880);
		theory = theory.withAxiom(x879);

		Term x882 = Term.mkApp("TO/Ord.Next", x8, x44, x17);
		Term x881 = Term.mkNot(x882);
		theory = theory.withAxiom(x881);

		Var x884 = Term.mkVar("looplessPath_t_1");
		Term x887 = Term.mkApp("this/Time", x884);
		Var x892 = Term.mkVar("var_72");
		Var x895 = Term.mkVar("var_73");
		Term x897 = Term.mkApp("TO/Ord", x895);
		Term x898 = Term.mkApp("TO/Ord.Next", x895, x884, x892);
		Term x896 = Term.mkAnd(x897, x898);
		Term x894 = Term.mkExists(List.of(x895.of(x4)), x896);
		Term x899 = Term.mkApp("this/Time", x892);
		Term x893 = Term.mkAnd(x894, x899);
		Term x891 = Term.mkExists(List.of(x892.of(x2)), x893);
		Term x890 = Term.mkNot(x891);
		Term x889 = Term.mkAnd(x887, x890);
		Term x888 = Term.mkNot(x889);
		Term x886 = Term.mkAnd(x887, x888);
		Var x901 = Term.mkVar("looplessPath_p_1");
		Term x903 = Term.mkApp("this/Process", x901);
		Var x907 = Term.mkVar("step_id_0");
		Term x909 = Term.mkApp("this/Process.toSend", x901, x907, x884);
		Var x912 = Term.mkVar("var_75");
		Var x915 = Term.mkVar("var_76");
		Term x917 = Term.mkApp("this/Process.toSend", x901, x912, x915);
		Var x919 = Term.mkVar("var_77");
		Term x921 = Term.mkApp("TO/Ord", x919);
		Term x922 = Term.mkApp("TO/Ord.Next", x919, x884, x915);
		Term x920 = Term.mkAnd(x921, x922);
		Term x918 = Term.mkExists(List.of(x919.of(x4)), x920);
		Term x916 = Term.mkAnd(x917, x918);
		Term x914 = Term.mkExists(List.of(x915.of(x2)), x916);
		Term x924 = Term.mkApp("this/Process.toSend", x901, x912, x884);
		Term x926 = Term.mkEq(x912, x907);
		Term x925 = Term.mkNot(x926);
		Term x923 = Term.mkAnd(x924, x925);
		Term x913 = Term.mkIff(x914, x923);
		Term x911 = Term.mkForall(List.of(x912.of(x3)), x913);
		Var x928 = Term.mkVar("var_78");
		Var x931 = Term.mkVar("var_79");
		Var x934 = Term.mkVar("var_80");
		Term x936 = Term.mkApp("this/Process.succ", x901, x934);
		Term x937 = Term.mkApp("this/Process.toSend", x934, x928, x931);
		Term x935 = Term.mkAnd(x936, x937);
		Term x933 = Term.mkExists(List.of(x934.of(x3)), x935);
		Var x939 = Term.mkVar("var_81");
		Term x941 = Term.mkApp("TO/Ord", x939);
		Term x942 = Term.mkApp("TO/Ord.Next", x939, x884, x931);
		Term x940 = Term.mkAnd(x941, x942);
		Term x938 = Term.mkExists(List.of(x939.of(x4)), x940);
		Term x932 = Term.mkAnd(x933, x938);
		Term x930 = Term.mkExists(List.of(x931.of(x2)), x932);
		Var x945 = Term.mkVar("var_82");
		Term x947 = Term.mkApp("this/Process.succ", x901, x945);
		Term x948 = Term.mkApp("this/Process.toSend", x945, x928, x884);
		Term x946 = Term.mkAnd(x947, x948);
		Term x944 = Term.mkExists(List.of(x945.of(x3)), x946);
		Term x950 = Term.mkEq(x928, x907);
		Var x953 = Term.mkVar("var_84");
		Term x955 = Term.mkApp("this/Process.succ", x901, x953);
		Term x956 = Term.mkClosure((App) Term.mkApp("func_1", x953, x928), x953, x928);
		Term x954 = Term.mkAnd(x955, x956);
		Term x952 = Term.mkExists(List.of(x953.of(x3)), x954);
		Term x951 = Term.mkNot(x952);
		Term x949 = Term.mkAnd(x950, x951);
		Term x943 = Term.mkOr(x944, x949);
		Term x929 = Term.mkIff(x930, x943);
		Term x927 = Term.mkForall(List.of(x928.of(x3)), x929);
		Term x910 = Term.mkAnd(x911, x927);
		Term x908 = Term.mkAnd(x909, x910);
		Term x906 = Term.mkExists(List.of(x907.of(x3)), x908);
		Var x958 = Term.mkVar("step_id_1");
		Var x961 = Term.mkVar("var_91");
		Term x963 = Term.mkApp("this/Process.succ", x961, x901);
		Term x964 = Term.mkApp("this/Process.toSend", x961, x958, x884);
		Term x962 = Term.mkAnd(x963, x964);
		Term x960 = Term.mkExists(List.of(x961.of(x3)), x962);
		Var x967 = Term.mkVar("var_92");
		Var x970 = Term.mkVar("var_93");
		Var x973 = Term.mkVar("var_94");
		Term x975 = Term.mkApp("this/Process.succ", x973, x901);
		Term x976 = Term.mkApp("this/Process.toSend", x973, x967, x970);
		Term x974 = Term.mkAnd(x975, x976);
		Term x972 = Term.mkExists(List.of(x973.of(x3)), x974);
		Var x978 = Term.mkVar("var_95");
		Term x980 = Term.mkApp("TO/Ord", x978);
		Term x981 = Term.mkApp("TO/Ord.Next", x978, x884, x970);
		Term x979 = Term.mkAnd(x980, x981);
		Term x977 = Term.mkExists(List.of(x978.of(x4)), x979);
		Term x971 = Term.mkAnd(x972, x977);
		Term x969 = Term.mkExists(List.of(x970.of(x2)), x971);
		Var x984 = Term.mkVar("var_96");
		Term x986 = Term.mkApp("this/Process.succ", x984, x901);
		Term x987 = Term.mkApp("this/Process.toSend", x984, x967, x884);
		Term x985 = Term.mkAnd(x986, x987);
		Term x983 = Term.mkExists(List.of(x984.of(x3)), x985);
		Term x989 = Term.mkEq(x967, x958);
		Term x988 = Term.mkNot(x989);
		Term x982 = Term.mkAnd(x983, x988);
		Term x968 = Term.mkIff(x969, x982);
		Term x966 = Term.mkForall(List.of(x967.of(x3)), x968);
		Var x991 = Term.mkVar("var_97");
		Var x994 = Term.mkVar("var_98");
		Var x997 = Term.mkVar("var_99");
		Var x1000 = Term.mkVar("var_100");
		Term x1002 = Term.mkApp("this/Process.succ", x1000, x901);
		Term x1003 = Term.mkApp("this/Process.succ", x1000, x997);
		Term x1001 = Term.mkAnd(x1002, x1003);
		Term x999 = Term.mkExists(List.of(x1000.of(x3)), x1001);
		Term x1004 = Term.mkApp("this/Process.toSend", x997, x991, x994);
		Term x998 = Term.mkAnd(x999, x1004);
		Term x996 = Term.mkExists(List.of(x997.of(x3)), x998);
		Var x1006 = Term.mkVar("var_101");
		Term x1008 = Term.mkApp("TO/Ord", x1006);
		Term x1009 = Term.mkApp("TO/Ord.Next", x1006, x884, x994);
		Term x1007 = Term.mkAnd(x1008, x1009);
		Term x1005 = Term.mkExists(List.of(x1006.of(x4)), x1007);
		Term x995 = Term.mkAnd(x996, x1005);
		Term x993 = Term.mkExists(List.of(x994.of(x2)), x995);
		Var x1012 = Term.mkVar("var_102");
		Var x1015 = Term.mkVar("var_103");
		Term x1017 = Term.mkApp("this/Process.succ", x1015, x901);
		Term x1018 = Term.mkApp("this/Process.succ", x1015, x1012);
		Term x1016 = Term.mkAnd(x1017, x1018);
		Term x1014 = Term.mkExists(List.of(x1015.of(x3)), x1016);
		Term x1019 = Term.mkApp("this/Process.toSend", x1012, x991, x884);
		Term x1013 = Term.mkAnd(x1014, x1019);
		Term x1011 = Term.mkExists(List.of(x1012.of(x3)), x1013);
		Term x1021 = Term.mkEq(x991, x958);
		Var x1024 = Term.mkVar("var_105");
		Var x1027 = Term.mkVar("var_106");
		Term x1029 = Term.mkApp("this/Process.succ", x1027, x901);
		Term x1030 = Term.mkApp("this/Process.succ", x1027, x1024);
		Term x1028 = Term.mkAnd(x1029, x1030);
		Term x1026 = Term.mkExists(List.of(x1027.of(x3)), x1028);
		Term x1031 = Term.mkClosure((App) Term.mkApp("func_1", x1024, x991), x1024, x991);
		Term x1025 = Term.mkAnd(x1026, x1031);
		Term x1023 = Term.mkExists(List.of(x1024.of(x3)), x1025);
		Term x1022 = Term.mkNot(x1023);
		Term x1020 = Term.mkAnd(x1021, x1022);
		Term x1010 = Term.mkOr(x1011, x1020);
		Term x992 = Term.mkIff(x993, x1010);
		Term x990 = Term.mkForall(List.of(x991.of(x3)), x992);
		Term x965 = Term.mkAnd(x966, x990);
		Term x959 = Term.mkAnd(x960, x965);
		Term x957 = Term.mkExists(List.of(x958.of(x3)), x959);
		Term x905 = Term.mkOr(x906, x957);
		Var x1033 = Term.mkVar("var_109");
		Term x1035 = Term.mkApp("this/Process.toSend", x901, x1033, x884);
		Var x1037 = Term.mkVar("var_110");
		Term x1039 = Term.mkApp("this/Process.toSend", x901, x1033, x1037);
		Var x1041 = Term.mkVar("var_111");
		Term x1043 = Term.mkApp("TO/Ord", x1041);
		Term x1044 = Term.mkApp("TO/Ord.Next", x1041, x884, x1037);
		Term x1042 = Term.mkAnd(x1043, x1044);
		Term x1040 = Term.mkExists(List.of(x1041.of(x4)), x1042);
		Term x1038 = Term.mkAnd(x1039, x1040);
		Term x1036 = Term.mkExists(List.of(x1037.of(x2)), x1038);
		Term x1034 = Term.mkIff(x1035, x1036);
		Term x1032 = Term.mkForall(List.of(x1033.of(x3)), x1034);
		Term x904 = Term.mkOr(x905, x1032);
		Term x902 = Term.mkImp(x903, x904);
		Term x900 = Term.mkForall(List.of(x901.of(x3)), x902);
		Term x885 = Term.mkImp(x886, x900);
		Term x883 = Term.mkForall(List.of(x884.of(x2)), x885);
		theory = theory.withAxiom(x883);

		Term x1046 = Term.mkApp("TO/Ord.Next", x8, x80, x9);
		Term x1045 = Term.mkNot(x1046);
		theory = theory.withAxiom(x1045);

		Term x1047 = Term.mkApp("TO/Ord.Next", x8, x44, x21);
		theory = theory.withAxiom(x1047);

		Term x1049 = Term.mkApp("TO/Ord.Next", x8, x32, x17);
		Term x1048 = Term.mkNot(x1049);
		theory = theory.withAxiom(x1048);

		Term x1051 = Term.mkApp("TO/Ord.Next", x8, x9, x44);
		Term x1050 = Term.mkNot(x1051);
		theory = theory.withAxiom(x1050);

		ModelFinder finder = new FortressTWO();
		finder.setTheory(theory);
		finder.setAnalysisScope(x2, 13);
		finder.setAnalysisScope(x3, 3);
		finder.setAnalysisScope(x4, 1);
		finder.setAnalysisScope(x5, 1);
		try{
			ModelFinderResult res = finder.checkSat();
			if (res.equals(ModelFinderResult.Sat())) { System.out.println(finder.viewModel()); }
		} catch (Exception e) { e.printStackTrace(); }
		System.out.println("*************************FINISH*****************************");
	}
}
