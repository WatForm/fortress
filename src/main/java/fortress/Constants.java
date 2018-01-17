/*
 * Copyright (c) 2016, Amirhossein Vakili
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 *    1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 *    2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package fortress;

import java.util.HashMap;
import java.util.Map;

/**
 * Created by Amirhossein Vakili.
 */
public final class Constants {

    private Constants(){}

    public static final String FN_Str = "->";

    public static final String PAIR_Str = "#";

    public static final String pair_Str = "#";

    public static final String BOOL_Str = "Bool";

    public static final String EQ_Str = "=";

    public static final String TRUE_Str = "true";

    public static final String FALSE_Str = "false";

    public static final String NOT_Str = "!";

    public static final String AND_Str = "&";

    public static final String OR_Str = "|";

    public static final String IMP_Str = "=>";

    public static final String IFF_Str = "<=>";

    public static final String FORALL_Str = "forall";

    public static final String EXISTS_Str = "exists";

    public static final String INTEGER_Str = "Int";

    public static final String NAT_Str = "Nat";

    public static final String ABS_Str = "abs";

    public static final String ADD_Str = "+";

    public static final String SUB_Str = "-";

    public static final String MUL_Str = "*";

    public static final String DIV_Str = "div";

    public static final String MOD_Str = "mode";

    public static final String LESS_Str = "<";

    public static final String GREATER_Str = ">";

    public static final String LESS_OR_EQ_Str = "<=";

    public static final String GREATER_OR_EQ_Str = ">=";

    public final static Map<String, String> smtlibOf = createSMTLIBOf();

    private static final Map<String, String> createSMTLIBOf(){
        Map<String, String> result = new HashMap<>();
        //result.put(BOOL_Str, "Bool");
        result.put(NOT_Str, "not");
        result.put(AND_Str, "and");
        result.put(OR_Str, "or");
        result.put(IFF_Str, "=");
        return result;
    }
}
