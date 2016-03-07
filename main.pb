;silly loop
;(progn (setq top 50000000) (setq n 0) (setq t1 (em)) (while (> top (setq n (+ n 1 ))) ) (- (em) t1 ) )
; +3 minutes -> 2.1 minutes
EnableExplicit

#HEAPSIZE  =	65536
#FREESIZE  =	16384
#STACKSIZE =	32768
#SYMSIZE	 =	256
#BUFSIZE	 =	256
#nil		 =	0
#T		 =	4
#READ_ERROR = -32
#EVAL_ERROR = -64
#APPLY_ERROR = -65
#SUBR_ERROR = -65
#EVLIS_ERROR = -66
#CHECK_ERROR = -67

;error code
Enumeration
	#NONE_ERR
	#CANT_FIND_ERR
	#ARG_SYM_ERR
	#ARG_NUM_ERR
	#ARG_STR_ERR
	#ARG_LIS_ERR
	#ARG_LEN0_ERR
	#ARG_LEN1_ERR
	#ARG_LEN2_ERR
	#ARG_LEN3_ERR
	#MALFORM_ERR
	#CANT_READ_ERR
	#ILLEGAL_OBJ_ERR
	#MISSING_QUOTE_ERR
EndEnumeration

;arg check codex
Enumeration
	#TEST_NONE
	#TEST_NUMLIST
	#TEST_SYMBOL
	#TEST_STRING
	#TEST_NUMBER
	#TEST_LIST
	#TEST_LEN0
	#TEST_LEN1
	#TEST_LEN2
	#TEST_LEN3
	#TEST_LENS1
	#TEST_LENS2
	#TEST_COND
EndEnumeration

Enumeration
	#TAG_EMP
	#TAG_NUM
	#TAG_SYM
	#TAG_LIS
	#TAG_SUBR
	#TAG_FSUBR
	#TAG_FUNC
	#TAG_STR
EndEnumeration

Enumeration
	#FLAG_FRE
	#FLAG_USE
EndEnumeration

Enumeration
	#TOKTYPE_LPAREN
	#TOKTYPE_RPAREN
	#TOKTYPE_QUOTE
	#TOKTYPE_DOT
	#TOKTYPE_NUMBER
	#TOKTYPE_SYMBOL
	#TOKTYPE_STRING
	#TOKTYPE_STRINGERR
	#TOKTYPE_OTHER
EndEnumeration

Enumeration
	#BACKTRACK_GO
	#BACKTRACK_BACK	
EndEnumeration

Macro GET_CAR(addr) 	: heap(addr)\car : EndMacro
Macro GET_CDR(addr) 	: heap(addr)\cdr : EndMacro
Macro GET_TAG(addr)		: heap(addr)\tag : EndMacro
Macro GET_NAME(addr)	: heap(addr)\name : EndMacro
Macro GET_NUMBER(addr)	: heap(addr)\num : EndMacro
Macro GET_BIND(addr)	: heap(addr)\bind : EndMacro
Macro GET_SUBR(addr)	: heap(addr)\subroutine : EndMacro
Macro SET_CAR(addr,x)	: heap(addr)\car = x : EndMacro
Macro SET_CDR(addr,x) 	: heap(addr)\cdr = x : EndMacro
Macro SET_TAG(addr,x) 	: heap(addr)\tag = x : EndMacro
Macro SET_NUMBER(addr,x) : heap(addr)\num = x : EndMacro
Macro SET_NAME(addr, x) 	: heap(addr)\name = x : EndMacro
Macro SET_SUBR(addr, x)  : heap(addr)\subroutine = x : EndMacro
Macro SET_BIND(addr, x)	: heap(addr)\bind = x : EndMacro
Macro IS_SYMBOL(addr) 	: heap(addr)\tag = #TAG_SYM : EndMacro
Macro IS_NUMBER(addr) 	: heap(addr)\tag = #TAG_NUM : EndMacro
Macro IS_STRING(addr)	: heap(addr)\tag = #TAG_STR : EndMacro
Macro IS_NIL(addr)		: addr = 0 Or addr = 1 : EndMacro
Macro IS_NOT_NIL(addr)  : addr <> 0 And addr <> 1 : EndMacro
Macro IS_LIST(addr)		: heap(addr)\tag = #TAG_LIS : EndMacro
Macro MARK_CELL(addr)	: heap(addr)\flag = #FLAG_USE : EndMacro
Macro NOMARK_CELL(addr)	: heap(addr)\flag = #FLAG_FRE : EndMacro


Macro ArgPop() : ap-1 : EndMacro
Macro ArgPush(addr) : argstk(ap) = addr : ap + 1 : EndMacro
; Procedure ArgPop()
; 	ap-1
; EndProcedure
; 
; Procedure ArgPush(addr.i)
; 	argstk(ap) = addr
; 	ap+1
; EndProcedure


Macro CFLOAT : "([+-]?)(?=\d|\.\d)\d*(\.\d*)?([Ee]([+-]?\d+))?" : EndMacro
Macro SYMBOL : "[a-zA-Z\_\+|\-|\*|\/|\>\=|\>|\<\=|\<|\=|\!\=|\%|\^]+[a-zA-Z0-9\-\_\+\-\*\/\#\%\$]*" : EndMacro
Macro STRING_ : #DOUBLEQUOTE$ + "(?:[^" + #DOUBLEQUOTE$ + "\\]|\\.)*" + #DOUBLEQUOTE$ : EndMacro

Structure Cell
	tag.b
	flag.b
	name.i
	StructureUnion
		num.i
		bind.i
		subroutine.i
	EndStructureUnion
	car.i
	cdr.i
EndStructure

Structure NameCode
	name.s
	code.i
EndStructure

Structure Token
	ch.c
	backtrack_flag.b
	toktype_type.b
	buf.s	;token string
EndStructure

Global NewList NameTable.NameCode()
#QUOTE_CODE = 1
Global global_namecounter = 2

Global current_line.s
Global current_line_index.i = 1

Global string_memory_total.i = 0

Global ep.i; //environment pointer
Global hp.i; //heap pointer 
Global sp.i; //stack pointer
Global fc.i; //free counter
Global ap.i; //arglist pointer
Global Dim heap.Cell(#HEAPSIZE)
Global Dim stack.i(#STACKSIZE)
Global Dim argstk.i(#STACKSIZE)
Global stok.Token
stok\backtrack_flag = #BACKTRACK_GO
stok\toktype_type = #TOKTYPE_OTHER

Declare PrintS(addr.i)
Declare ReadList()
Declare Eval(addr.i)
Declare Nullp(addr)
Declare eqp(addr1.i,addr2.i)
Declare Is_Empty(addr.i)
Declare Is_Func(addr.I)
Declare Car(addr)
Declare Cdr(addr)
Declare Used_Cell(addr)
Declare Free_Cell(addr)
Declare SymbolP(addr.i)
Declare NumberP(addr.i)
Declare ListP(addr.i)
Declare StringP(addr.i)
Declare ResetInputBuffer()

Procedure GetNameCode(name.s)
	Debug global_namecounter
	ForEach NameTable()
		If name = NameTable()\name
			ProcedureReturn NameTable()\code
		EndIf
	Next
	
	AddElement(NameTable())
	If name.s = "quote"
		NameTable()\code = #QUOTE_CODE
	Else
		NameTable()\code = global_namecounter
	EndIf
	NameTable()\name = name.s
	global_namecounter + 1
	ProcedureReturn NameTable()\code	
EndProcedure

Procedure.s GetNameStrFromCode(code.i)
	ForEach NameTable()
		If NameTable()\code = code
			ProcedureReturn NameTable()\name
		EndIf
	Next
EndProcedure

Procedure Print_(msg.s, newline.b = 1)
	If newline
		PrintN(msg)
	Else
		Print(msg)
	EndIf
	ProcedureReturn #True
EndProcedure

Procedure Error(errnum.i, fun.s, arg.i)
	Select errnum
		Case #CANT_FIND_ERR		: Print_(fun + " can't find definition of ",0) 		: PrintS(arg)
		Case #CANT_READ_ERR		: Print_(fun + " can't read ",0)					: PrintS(arg)
		Case #MISSING_QUOTE_ERR	: Print_(fun + " is missing a quote ", 0)			: PrintS(arg)
		Case #ILLEGAL_OBJ_ERR	: Print_(fun + " received an illegal object ",0)		: PrintS(arg)
		Case #ARG_SYM_ERR		: Print_(fun + " requires a symbol but received ", 0)	: PrintS(arg)
		Case #ARG_NUM_ERR		: Print_(fun + " requires a number but received ", 0)	: PrintS(arg)
		Case #ARG_STR_ERR        : Print_(fun + " requres a string but recieved ", 0)   : PrintS(arg)
		Case #ARG_LIS_ERR		: Print_(fun + " requires a list but received ", 0)	: PrintS(arg)
		Case #ARG_LEN0_ERR		: Print_(fun + " requires 0 arg but received ", 0)	: PrintS(arg)
		Case #ARG_LEN1_ERR		: Print_(fun + " requires 1 arg but received ", 0)	: PrintS(arg)
		Case #ARG_LEN2_ERR		: Print_(fun + " requires 2 arg but received ", 0)	: PrintS(arg)
		Case #ARG_LEN3_ERR		: Print_(fun + " requires 3 arg but received ", 0)	: PrintS(arg)
		Case #MALFORM_ERR		: Print_(fun + " received malformed args ", 0)		: PrintS(arg)
	EndSelect
	Print_("") ;newline
	ProcedureReturn 0
EndProcedure

Procedure Length(addr.i)
	Define len.i = 0
	While Nullp(addr) = #False
		len + 1
		addr = cdr(addr)
	Wend
	ProcedureReturn len
EndProcedure

Procedure IsNumLis(arg.i)
	While IS_NOT_NIL(arg)
		If NumberP(car(arg))
			arg = cdr(arg)
		Else
			ProcedureReturn 0
		EndIf	
	Wend
	ProcedureReturn 1
EndProcedure

Procedure CheckArgs(test.b, fun.s, arg.i)
	;ProcedureReturn #True
	Select test
			Case #TEST_NUMLIST	:	If IsNumLis(arg)	:	ProcedureReturn #True	: Else	: Error(#ARG_NUM_ERR,fun,arg) : ProcedureReturn #CHECK_ERROR : EndIf
			Case #TEST_SYMBOL	:	If SymbolP(arg)	:	ProcedureReturn #True	: Else	: Error(#ARG_SYM_ERR,fun,arg) : ProcedureReturn #CHECK_ERROR : EndIf
			Case #TEST_NUMBER	:	If NumberP(arg)	:	ProcedureReturn #True	: Else	: Error(#ARG_NUM_ERR,fun,arg) : ProcedureReturn #CHECK_ERROR : EndIf
			Case #TEST_STRING	:	If StringP(arg)	:	ProcedureReturn #True	: Else	: Error(#ARG_STR_ERR,fun,arg)	: ProcedureReturn #CHECK_ERROR : EndIf
			Case #TEST_LIST	:	If ListP(arg)		:	ProcedureReturn #True	: Else	: Error(#ARG_LIS_ERR,fun,arg) : ProcedureReturn #CHECK_ERROR : EndIf
			Case #TEST_LEN0	:	If Length(arg) = 0	:	ProcedureReturn #True	: Else	: Error(#ARG_LEN0_ERR,fun,arg): ProcedureReturn #CHECK_ERROR : EndIf
			Case #TEST_LEN1	:	If Length(arg) = 1	:	ProcedureReturn #True	: Else	: Error(#ARG_LEN1_ERR,fun,arg): ProcedureReturn #CHECK_ERROR : EndIf
			Case #TEST_LEN2	:	If Length(arg) = 2	:	ProcedureReturn #True	: Else	: Error(#ARG_LEN2_ERR,fun,arg): ProcedureReturn #CHECK_ERROR : EndIf
			Case #TEST_LEN3	:	If Length(arg) = 3	:	ProcedureReturn #True	: Else	: Error(#ARG_LEN3_ERR,fun,arg): ProcedureReturn #CHECK_ERROR : EndIf
	EndSelect
	ProcedureReturn #SUBR_ERROR
EndProcedure

Procedure MarkObList()
	Define addr.i
	addr = ep
	While NullP(addr) = #False
		MARK_CELL(addr)
		addr = cdr(addr)
	Wend
	MARK_CELL(0)
EndProcedure

Procedure MarkCell(addr.i)
	If Used_Cell(addr) : ProcedureReturn 0 : EndIf
	
	MARK_CELL(addr)
	If car(addr) <> 0
		MarkCell(car(addr))
	EndIf
	
	If cdr(addr) <> 0
		MarkCell(cdr(addr))
	EndIf
	
	If GET_BIND(addr) <> 0 And Is_Func(addr)
		MarkCell(GET_BIND(addr))
	EndIf
EndProcedure

Procedure GbcMark()
	Define addr.i, i.i
	MarkObList()
	addr = ep
	While Nullp(addr) = #False
		MarkCell(car(addr))
		addr = cdr(addr)
	Wend
	i = 0
	While i < ap		
		MarkCell(argstk(i))
		i + 1
	Wend
EndProcedure

Procedure ClrCell(addr.i)
	If GET_TAG(addr) = #TAG_STR : FreeMemory(GET_NUMBER(addr)) : EndIf 
	SET_TAG(addr, #TAG_EMP)
	heap(addr)\name = 0
	SET_CAR(addr,0)
	SET_CDR(addr,0)	
	SET_BIND(addr,0)
EndProcedure

Procedure GbcSweep()
	Define addr.i
	addr = 0
	While addr <= #HEAPSIZE
		If Used_Cell(addr)
			NOMARK_CELL(addr)
		Else
			ClrCell(addr)
			SET_CDR(addr, hp)
			hp = addr		
		EndIf
		addr + 1
	Wend
EndProcedure

Procedure GBC()
	Define addr.i
	;PrintN("enter GBC free= " + Str(fc))
	
	GbcMark()
	GbcSweep()
	fc = 0
	
	addr = 0
	While addr <= #HEAPSIZE
		If Is_Empty(addr) : fc + 1 : EndIf
		addr + 1
	Wend
	
	;PrintN("exit GBC free= " + Str(fc))
EndProcedure

Procedure Push(pt.i)
	stack(sp) = pt ;stack[sp++] = pt 
	sp + 1
EndProcedure

Procedure Pop()
	sp - 1         ;stack[--sp] 
	ProcedureReturn stack(sp)
EndProcedure

Procedure Used_Cell(addr)
	If heap(addr)\flag = #FLAG_USE
		ProcedureReturn 1
	EndIf
	ProcedureReturn 0
EndProcedure

Procedure Free_Cell(addr)
	If heap(addr)\flag = #FLAG_FRE
		ProcedureReturn 1
	EndIf
	ProcedureReturn 0
EndProcedure

Procedure Is_Subr(addr.i)
	If heap(addr)\tag = #TAG_SUBR : ProcedureReturn 1 : EndIf
	ProcedureReturn 0
EndProcedure

Procedure Is_FSubr(addr.i)
	If heap(addr)\tag = #TAG_FSUBR : ProcedureReturn 1 : EndIf
	ProcedureReturn 0
EndProcedure

Procedure Is_Func(addr.i)
	If heap(addr)\tag = #TAG_FUNC : ProcedureReturn 1 : EndIf
	ProcedureReturn 0
EndProcedure

Procedure Is_Empty(addr.i)
	If heap(addr)\tag = #TAG_EMP : ProcedureReturn 1 : EndIf
	ProcedureReturn 0
EndProcedure

Procedure Has_Name(addr.i, x.i)
	If heap(addr)\name = x
		ProcedureReturn #True
	Else
		ProcedureReturn #False
	EndIf
EndProcedure

Procedure.c GetChar()
	Define r.c = Asc(Mid(current_line, current_line_index, 1))
	If current_line_index >= Len(current_line)
		current_line_index = 0
		current_line = ""
	EndIf
	current_line_index + 1
	ProcedureReturn r
EndProcedure

Procedure StringToken(buff.s)
	Define regex_symbol = CreateRegularExpression(#PB_Any, STRING_)
	If MatchRegularExpression(regex_symbol, buff)
		FreeRegularExpression(regex_symbol)
		ProcedureReturn #True
	EndIf
	FreeRegularExpression(regex_symbol)
	ProcedureReturn #False
EndProcedure

Procedure NumberToken(buff.s)
	Define regex_cfloat = CreateRegularExpression(#PB_Any, "^"+ CFLOAT + "$")
	If MatchRegularExpression(regex_cfloat, buff)
		FreeRegularExpression(regex_cfloat)
		ProcedureReturn #True
	EndIf
	FreeRegularExpression(regex_cfloat)
	ProcedureReturn #False
EndProcedure

Procedure SymbolToken(buff.s)
	Define regex_symbol = CreateRegularExpression(#PB_Any, SYMBOL)
	If MatchRegularExpression(regex_symbol, buff)
		FreeRegularExpression(regex_symbol)
		ProcedureReturn #True
	EndIf
	FreeRegularExpression(regex_symbol)
	ProcedureReturn #False
EndProcedure

Procedure FreshCell()
	Define res.i
	res = hp
	hp = heap(hp)\cdr ;set heap pointer to next free cell
	SET_CDR(res,0)
	fc - 1
	ProcedureReturn res
EndProcedure

Procedure Cons(car.i, cdr.i)
	Define addr.i
	addr = FreshCell()
	SET_TAG(addr, #TAG_LIS)
	SET_CAR(addr, car)
	SET_CDR(addr, cdr)
	ProcedureReturn addr
EndProcedure

Procedure Car(addr) : ProcedureReturn GET_CAR(addr) : EndProcedure
Procedure Cdr(addr) : ProcedureReturn GET_CDR(addr) : EndProcedure
Procedure Caar(addr) : ProcedureReturn car(car(addr)) : EndProcedure
Procedure Cdar(addr) : ProcedureReturn cdr(car(addr)) : EndProcedure
Procedure Cadr(addr) : ProcedureReturn car(cdr(addr)) : EndProcedure
Procedure Caddr(addr) : ProcedureReturn car(cdr(cdr(addr))) : EndProcedure

Procedure MakeNum(num.i)
	Define addr.i
	addr = FreshCell()
	SET_TAG(addr,#TAG_NUM)
	SET_NUMBER(addr,num)
	ProcedureReturn addr
EndProcedure

Procedure MakeStr(str.s)
	Define addr = FreshCell()
	SET_TAG(addr, #TAG_STR)
	CompilerIf #PB_Compiler_Unicode 
		Define *mem = AllocateMemory( (Len(str) + 1) * 2 )
	CompilerElse
		Define *mem = AllocateMemory(Len(str) + 1)
	CompilerEndIf
	PokeS(*mem, str)
	SET_NUMBER(addr, *mem)
	ProcedureReturn addr
EndProcedure

Procedure MakeSym(namecode.i)
	Define addr.i
	addr = FreshCell()
	SET_TAG(addr, #TAG_SYM)
	SET_NAME(addr, namecode)
	ProcedureReturn addr
EndProcedure

Procedure AssocSym(sym.i, val.i)
	ep = cons(cons(sym, val), ep)
EndProcedure

Procedure Assoc(sym.i, lis.i)
	If Nullp(lis)
		ProcedureReturn 0
	ElseIf eqp(sym, caar(lis))
		ProcedureReturn car(lis)		
	Else
		ProcedureReturn assoc(sym, cdr(lis))
	EndIf
EndProcedure

Procedure Atomp(addr.i)
	If IS_NUMBER(addr) Or IS_SYMBOL(addr) Or IS_STRING(addr)
		ProcedureReturn #True
	Else
		ProcedureReturn #False
	EndIf
EndProcedure

Procedure NumberP(addr.i)
	If IS_NUMBER(addr)
		ProcedureReturn #True
	Else
		ProcedureReturn #False
	EndIf
EndProcedure

Procedure SymbolP(addr.i)
	If IS_SYMBOL(addr)
		ProcedureReturn #True
	Else
		ProcedureReturn #False
	EndIf
EndProcedure

Procedure StringP(addr.i)
	If IS_STRING(addr)
		ProcedureReturn #True
	Else
		ProcedureReturn #False
	EndIf
EndProcedure

Procedure Listp(addr)
	If IS_LIST(addr)
		ProcedureReturn #True
	Else
		ProcedureReturn #False
	EndIf
EndProcedure

Procedure Nullp(addr)
	If IS_NIL(addr)
		ProcedureReturn #True
	Else
		ProcedureReturn #False
	EndIf
EndProcedure


Procedure GetToken()
	Define c.c
	If stok\backtrack_flag = #BACKTRACK_BACK
		stok\backtrack_flag = #BACKTRACK_GO
		ProcedureReturn #True
	EndIf
	
	If stok\ch = ')'
		stok\toktype_type = #TOKTYPE_RPAREN
		stok\ch = #Null
		ProcedureReturn #True
	EndIf
	
	If stok\ch = '('
		stok\toktype_type = #TOKTYPE_LPAREN
		stok\ch = #Null
		ProcedureReturn #True
	EndIf
	
	c = GetChar()
	While c = ' ' Or c = #TAB;tab
		c=GetChar()	   ;skip whitespace
	Wend
	
	Select c
		Case '(' : stok\toktype_type = #TOKTYPE_LPAREN
		Case ')' : stok\toktype_type = #TOKTYPE_RPAREN
		Case 39  : stok\toktype_type = #TOKTYPE_QUOTE
		Case '.' : stok\toktype_type = #TOKTYPE_DOT
		Case '"' :
			Define max_line_len = Len(current_line)
			stok\buf = ""
			stok\buf = stok\buf + Chr(c)
			c = GetChar()
			Define inc = 0
			While c <> '"'
				stok\buf = stok\buf + Chr(c)
				c = GetChar()
				
				;prevent unquoted string
				inc + 1
				If inc > max_line_len
					stok\toktype_type = #TOKTYPE_STRINGERR
					stok\buf = ""
					ProcedureReturn #False
				EndIf
			Wend
			stok\buf = stok\buf + Chr(c) ;add end quote
			stok\ch = c
			
			If StringToken(stok\buf)
				stok\toktype_type = #TOKTYPE_STRING
			Else
				stok\toktype_type = #TOKTYPE_OTHER
			EndIf
		Default :
			stok\buf = ""
			stok\buf = stok\buf + Chr(c)
			c=GetChar()
			
			While c <> 0 And c <> ' ' And c <> '(' And c <> ')'
				stok\buf = stok\buf + Chr(c)
				c=GetChar()
			Wend
			
			stok\ch = c
			
			If NumberToken(stok\buf)
				stok\toktype_type = #TOKTYPE_NUMBER
			ElseIf SymbolToken(stok\buf)
				stok\toktype_type = #TOKTYPE_SYMBOL
			Else
				stok\toktype_type = #TOKTYPE_OTHER
			EndIf
	EndSelect
EndProcedure

Procedure Read_()
	GetToken()
	Select stok\toktype_type
		Case #TOKTYPE_NUMBER	:	ProcedureReturn MakeNum(Val(stok\buf))	
		Case #TOKTYPE_STRING	:	ProcedureReturn MakeStr(stok\buf)
		Case #TOKTYPE_SYMBOL	:	ProcedureReturn MakeSym(GetNameCode(stok\buf))
		Case #TOKTYPE_QUOTE		:	ProcedureReturn Cons(MakeSym(GetNameCode("quote")), cons(Read_(), #nil))
		Case #TOKTYPE_LPAREN	:	ProcedureReturn ReadList()
		Case #TOKTYPE_STRINGERR	:	Error(#MISSING_QUOTE_ERR, "read", #nil) : ProcedureReturn #READ_ERROR
	EndSelect
	Error(#CANT_READ_ERR, "read", #nil)
	ProcedureReturn #READ_ERROR
EndProcedure

Procedure ReadList()
	Define car.i, cdr.i
	GetToken()
	If stok\toktype_type = #TOKTYPE_RPAREN : ProcedureReturn #nil : EndIf
	
	If stok\toktype_type = #TOKTYPE_DOT
		cdr = Read_()
		If cdr = #READ_ERROR : ProcedureReturn #READ_ERROR : EndIf
		If Atomp(cdr) : GetToken() : EndIf
		ProcedureReturn cdr
	Else
		stok\backtrack_flag = #BACKTRACK_BACK
		car = Read_()
		If car = #READ_ERROR : ProcedureReturn #READ_ERROR : EndIf
		cdr = ReadList()
		If cdr = #READ_ERROR : ProcedureReturn #READ_ERROR : EndIf
		ProcedureReturn cons(car, cdr)
	EndIf
EndProcedure

Procedure PrintList(addr.i)
	If IS_NIL(addr)
		Print_(")",0)
		ProcedureReturn #True
	EndIf
	
	If listp(Cdr(addr)) = #False And Nullp(cdr(addr)) = #False
		PrintS(Car(addr))
		Print_(" . ", 0)
		PrintS(Cdr(addr))
		Print_(")", 0)
	Else
		PrintS(GET_CAR(addr))
		Define gcdr = GET_CDR(addr)
		If IS_NIL(gcdr)
			;do nothing
		Else
			print_(" ", 0)
		EndIf    
		PrintList(gcdr)
	EndIf
EndProcedure

Procedure PrintS(addr.i)
	Select GET_TAG(addr)
		Case #TAG_NUM	:	Print_(Str(GET_NUMBER(addr)), 0)
		Case #TAG_SYM	:	Print_(GetNameStrFromCode(GET_NAME(addr)), 0)
		Case #TAG_STR	:	Print_(PeekS(GET_NUMBER(addr)), 0)
		Case #TAG_SUBR	:	Print_("subr", 0)
		Case #TAG_FSUBR:	Print_("<fsubr>", 0)
		Case #TAG_FUNC	:	Print_("<function>", 0)
		Case #TAG_LIS	:	Print_("(", 0) : PrintList(addr)
		Default		:	Print_("<undef>", 0)
	EndSelect
EndProcedure

Procedure Same_Name(addr1, addr2)
	If heap(addr1)\name = heap(addr2)\name
		ProcedureReturn #True
	Else
		ProcedureReturn #False
	EndIf
EndProcedure

Procedure eqp(addr1.i, addr2.i)
	If heap(addr1)\tag = #TAG_NUM And heap(addr2)\tag = #TAG_NUM
		If GET_NUMBER(addr1) = GET_NUMBER(addr2)
			ProcedureReturn 1
		EndIf
	EndIf
	
	If heap(addr1)\tag = #TAG_SYM And heap(addr2)\tag = #TAG_SYM
		If heap(addr1)\name = heap(addr2)\name 
			ProcedureReturn 1
		EndIf	
	EndIf
	
	If heap(addr1)\tag = #TAG_STR And heap(addr2)\tag = #TAG_STR
		If GET_NUMBER(addr1) = GET_NUMBER(addr2)
			ProcedureReturn 1
		EndIf
	EndIf
	
	ProcedureReturn 0
EndProcedure
; 
; Procedure eqp(addr1.i, addr2.i)
; 	Define gnum1 = GET_NUMBER(addr1)
; 	Define gnum2 = GET_NUMBER(addr2)
; 	
; 	If NumberP(addr1) And NumberP(addr2) And gnum1 = gnum2
; 		ProcedureReturn 1
; 	ElseIf SymbolP(addr1) And Symbolp(addr2) And Same_Name(addr1,addr2)
; 		ProcedureReturn 1	
; 	Else
; 		ProcedureReturn 0
; 	EndIf
; EndProcedure

Procedure FindSym(sym.i)
	Define addr.i
	addr = Assoc(sym,ep)
	If addr = 0
		ProcedureReturn -1
	Else
		ProcedureReturn cdr(addr)
	EndIf
EndProcedure

Procedure FSubRp(addr.i)
	
	Define val.i
	val = FindSym(addr)
	If val <> -1
		ProcedureReturn IS_FSUBR(val)
	Else
		ProcedureReturn 0
	EndIf
EndProcedure

Procedure SubRp(addr.i)
	Define val.i
	val = FindSym(addr)
	If val <> -1
		ProcedureReturn Is_Subr(val)
	Else
		ProcedureReturn 0
	EndIf
EndProcedure

Procedure BindSym(sym.i, val.i)
	Define addr.i
	addr = Assoc(sym, ep)
	If addr = 0
		AssocSym(sym,val)
	Else
		SET_CDR(addr,val)
	EndIf    
EndProcedure

Procedure BindFunc(name.i, tag.b, func.i)
	Define sym.i, val.i
	sym = MakeSym(name)
	val = FreshCell()
	SET_TAG(val, tag)
	SET_SUBR(val, func)
	SET_CDR(val, 0)
	BindSym(sym,val)
EndProcedure	

Procedure BindFunc1(name.i, addr.i)
	Define sym.i, val.i
	sym = MakeSym(name)
	val = FreshCell()
	SET_TAG(val, #TAG_FUNC)
	SET_BIND(val, addr)
	SET_CDR(val, 0)
	BindSym(sym, val)
EndProcedure

Procedure DefSubr(symcode.i, func.i)
	BindFunc(symcode, #TAG_SUBR, func)
EndProcedure

Procedure DefFSubr(symcode.i, func.i)
	BindFunc(symcode, #TAG_FSUBR, func)
EndProcedure

Procedure FunctionP(addr.i)
	Define val.i
	val = FindSym(addr)
	If val <> -1
		ProcedureReturn IS_FUNC(val)
	Else
		ProcedureReturn 0
	EndIf
EndProcedure

Procedure BindArg(varlist.i, arglist.i)
	Define arg1.i, arg2.i
	push(ep)
	While IS_NOT_NIL(varlist)
		arg1 = car(varlist)
		arg2 = car(arglist)
		AssocSym(arg1, arg2)
		varlist = cdr(varlist)
		arglist = cdr(arglist)
	Wend
EndProcedure

Procedure UnBind()
	ep = pop()
EndProcedure

Prototype proto(arglist.i)
Procedure RunSubroutine(fn.proto, arglist.i)
	ProcedureReturn fn(arglist)
EndProcedure

Procedure Apply(func.i, args.i)
	Define symaddr.i, varlist.i, body.i, res.i
	symaddr = FindSym(func)
	If symaddr = -1
		Error(#CANT_FIND_ERR, "apply", func)
		ProcedureReturn #APPLY_ERROR
	Else
		Select GET_TAG(symaddr)
			Case #TAG_SUBR		: ProcedureReturn RunSubroutine(GET_SUBR(symaddr), args)		;get subroutine and run it with argument list
			Case #TAG_FSUBR	: ProcedureReturn RunSubroutine(GET_SUBR(symaddr), args)
			Case #TAG_FUNC
				varlist = car(GET_BIND(symaddr))
				body = cdr(GET_BIND(symaddr))
				BindArg(varlist, args)
				While IS_NOT_NIL(body)
					res = Eval(car(body))
					body = cdr(body)
				Wend
				UnBind()
				ProcedureReturn res
			Default
				Error(#ILLEGAL_OBJ_ERR, "eval", symaddr)
				ProcedureReturn #APPLY_ERROR
		EndSelect
	EndIf
EndProcedure

Procedure CheckGBC()
	If fc < #FREESIZE		
		gbc()
	EndIf
EndProcedure

Procedure Evlis(addr.i)
	Define car_addr.i, cdr_addr.i
	argpush(addr)
	CheckGBC()
	If IS_NIL(addr)
		argpop()
		ProcedureReturn addr
	Else
		car_addr = eval(car(addr))
		If car_addr = #EVAL_ERROR
			argpop()
			ProcedureReturn #EVLIS_ERROR
		EndIf
		
		argpush(car_addr)
		cdr_addr = evlis(cdr(addr))
		argpop()
		argpop()
		If cdr_addr = #EVLIS_ERROR
			ProcedureReturn #EVLIS_ERROR
		EndIf		
		ProcedureReturn cons(car_addr, cdr_addr)
	EndIf
EndProcedure

Procedure Eval(addr.i)
	Define res.i
	
	If atomp(addr)	;if it is an atom
		If NumberP(addr) : ProcedureReturn addr : EndIf	;return number if number
		If StringP(addr) : ProcedureReturn addr : EndIf
		If SymbolP(addr)							;lookup number if symbol
			Define res = FindSym(addr)
			If res = -1
				Error(#CANT_FIND_ERR, "eval", addr)
				ProcedureReturn #EVAL_ERROR
			Else
				ProcedureReturn res
			EndIf
		EndIf
	EndIf
	
	If listp(addr)
		If SymbolP(car(addr)) And Has_Name(car(addr), #QUOTE_CODE) ;if first element is quote return quoted part
			ProcedureReturn cadr(addr)
		EndIf
		
		If NumberP(car(addr)) ;if list start is number error (list must be a symbol)
			Error(#ARG_SYM_ERR, "eval", addr)
			ProcedureReturn #EVAL_ERROR
		EndIf	
		
		If SubRp(car(addr))
			Define arg1 = car(addr)
			ArgPush(arg1)
			Define arg2 = evlis(cdr(addr))
			If arg2 = #EVLIS_ERROR
				ArgPop()
				ProcedureReturn #EVAL_ERROR
			EndIf	
			ArgPush(arg2)
			Define r = Apply(arg1, arg2)
			ArgPop()
			ArgPop()
			If r = #APPLY_ERROR : ProcedureReturn #EVAL_ERROR : EndIf
			ProcedureReturn r
		EndIf	
		
		If FSubRp(car(addr))
			Define arg1 = car(addr)
			ArgPush(arg1)
			Define arg2 = cdr(addr)
			ArgPush(arg2)
			Define r = Apply(arg1, arg2)
			ArgPop()
			ArgPop()
			If r = #APPLY_ERROR : ProcedureReturn #EVAL_ERROR : EndIf
			ProcedureReturn r
		EndIf
		
		
		If FunctionP(car(addr))
			Define arg1 = car(addr)
			ArgPush(arg1)
			Define arg2 = evlis(cdr(addr))
			If arg2 = #EVLIS_ERROR
				ArgPop()
				ProcedureReturn #EVAL_ERROR
			EndIf
			ArgPush(arg2)
			Define r = Apply(arg1, arg2)
			ArgPop()
			ArgPop()
			If r = #APPLY_ERROR : ProcedureReturn #EVAL_ERROR : EndIf
			ProcedureReturn r
		EndIf
		
	EndIf
	
	Error(#CANT_FIND_ERR, "eval", addr)
	ProcedureReturn #EVAL_ERROR
EndProcedure

Procedure InitCell()
	Define addr.i, addr1.i
	
	addr = 0
	While addr < #HEAPSIZE
		heap(addr)\flag = #FLAG_FRE
		heap(addr)\cdr = addr + 1
		addr + 1
	Wend
	hp = 0
	fc = #HEAPSIZE
	
	ep = MakeSym(GetNameCode("nil"))
	AssocSym(MakeSym(GetNameCode("nil")), #nil)
	AssocSym(MakeSym(GetNameCode("t")), MakeSym(GetNameCode("t")))
	
	sp = 0
	ap = 0
EndProcedure

Macro F_NumCmp(op, f_name, f_name_str)
Procedure f_name(arglist)
	Define num1, num2
	If CheckArgs(#TEST_LEN2, f_name_str, arglist) = #CHECK_ERROR : ProcedureReturn #SUBR_ERROR : EndIf
	If CheckArgs(#TEST_NUMLIST, f_name_str, arglist) = #CHECK_ERROR : ProcedureReturn #SUBR_ERROR : EndIf
	num1 = GET_NUMBER(car(arglist))
	num2 = GET_NUMBER(cadr(arglist))
	If num1 op num2
		ProcedureReturn #T
	Else
		ProcedureReturn #nil
	EndIf
EndProcedure
EndMacro

F_NumCmp(=, F_Num_EQ, "=" )
F_NumCmp(>, F_Num_GT, ">" )
F_NumCmp(<, F_Num_LT, "<" )
F_NumCmp(>=,F_Num_GE, ">=" )
F_NumCmp(<=,F_Num_LE, "<=" )
F_NumCmp(<>,F_Num_NE, "<>" )

Macro F_Arith(op, f_name, f_name_str)
Procedure f_name(arglist.i)
	Define arg.i, res.i
	If CheckArgs(#TEST_NUMLIST, f_name_str, arglist) = #CHECK_ERROR
		ProcedureReturn #SUBR_ERROR
	EndIf
	res = GET_NUMBER(car(arglist))
	arglist = cdr(arglist)
	While IS_NOT_NIL(arglist)
		arg = GET_NUMBER(car(arglist))
		arglist = cdr(arglist)
		res = res op arg
	Wend	
	ProcedureReturn MakeNum(res)
EndProcedure
EndMacro

F_Arith(+, F_Plus, "+")
F_Arith(-, F_Minus, "-")
F_Arith(/, F_Div, "/")
F_Arith(*, F_Mul, "*")

Procedure F_Mod(arglist.i)
	Define arg.i, res.i
	If CheckArgs(#TEST_NUMLIST, "%", arglist) = #CHECK_ERROR
		ProcedureReturn #SUBR_ERROR
	EndIf
	res = GET_NUMBER(car(arglist))
	arglist = cdr(arglist)
	While IS_NOT_NIL(arglist)
		arg = GET_NUMBER(car(arglist))
		arglist = cdr(arglist)
		res = Mod(res, arg)
	Wend	
	ProcedureReturn MakeNum(res)
EndProcedure

Procedure F_Defun(arglist.i)
	Define arg1, arg2
	Define test1 = CheckArgs(#TEST_LEN3, "defun", arglist)
	Define test2 = CheckArgs(#TEST_SYMBOL, "defun", car(arglist))
	Define test3 = CheckArgs(#TEST_LIST, "defun", cadr(arglist))
	Define test4 = Checkargs(#TEST_LIST, "defun", caddr(arglist))
	If test1 = #CHECK_ERROR Or test2 = #CHECK_ERROR Or test3= #CHECK_ERROR Or test4 = #CHECK_ERROR
		ProcedureReturn #SUBR_ERROR
	EndIf
	
	arg1 = car(arglist)
	arg2 = cdr(arglist)
	Bindfunc1(GET_NAME(arg1), arg2)
	ProcedureReturn #T
EndProcedure

Procedure F_Eval(arglist.i)
	If CheckArgs(#TEST_LEN1, "eval", arglist) = #CHECK_ERROR : ProcedureReturn #SUBR_ERROR : EndIf
	ProcedureReturn eval(car(arglist))
EndProcedure

Procedure F_Apply(arglist.i)
     If CheckArgs(#TEST_LEN2, "apply", arglist) = #CHECK_ERROR : ProcedureReturn #SUBR_ERROR : EndIf
     If CheckArgs(#TEST_SYMBOL, "apply", car(arglist)) = #CHECK_ERROR : ProcedureReturn #SUBR_ERROR : EndIf
     If CheckArgs(#TEST_LIST, "apply", cadr(arglist)) = #CHECK_ERROR : ProcedureReturn #SUBR_ERROR : EndIf
     Define arg1.i, arg2.i
     arg1 = car(arglist)
     arg2 = cadr(arglist)
     ProcedureReturn Apply(arg1, arg2)
EndProcedure

Procedure F_NewLine(arglist.i)
     Print_("", 1)
     ProcedureReturn #T
EndProcedure

Procedure F_Print(arglist.i)
	If CheckArgs(#TEST_LEN1, "print", arglist) = #CHECK_ERROR : ProcedureReturn #SUBR_ERROR : EndIf
	Define addr = car(arglist)
	If GET_TAG(car(arglist)) = #TAG_STR
	     Print_(Trim(PeekS(GET_NUMBER(addr)), Chr(34)), 0)
	Else 
	     PrintS(addr)
	EndIf	
	ProcedureReturn #T
EndProcedure

Procedure F_If(arglist.i)
     Define arg1.i, arg2.i, arg3.i
     If CheckArgs(#TEST_LEN3, "if", arglist) = #CHECK_ERROR : ProcedureReturn #SUBR_ERROR : EndIf
     arg1 = car(arglist)
     arg2 = cadr(arglist)
     arg3 = car(cdr(cdr(arglist)))
     
     If NullP(eval(arg1)) = #False
          ProcedureReturn eval(arg2)
     Else
          ProcedureReturn eval(arg3)
     EndIf
EndProcedure

Declare F_Progn(arglist.i)
Declare F_Cond(arglist.i)

Procedure F_Cond(arglist.i)
     Define arg1.i, arg2.i, arg3.i
     If NullP(arglist)
          ProcedureReturn #nil
     EndIf
     
     arg1 = car(arglist)
     If CheckArgs(#TEST_LIST, "cond", arg1) = #CHECK_ERROR : ProcedureReturn #SUBR_ERROR : EndIf
     arg2 = car(arg1)
     arg3 = cdr(arg1)

     If NullP(eval(arg2)) = #False
          ProcedureReturn F_Progn(arg3)
     Else
          ProcedureReturn F_Cond(cdr(arglist))
     EndIf
EndProcedure

;( while () )
Procedure F_While(arglist.i)
	If CheckArgs(#TEST_LEN1, "while", arglist) = #CHECK_ERROR : ProcedureReturn #SUBR_ERROR : EndIf
	Define res.i
	Repeat
		res = Eval(car(arglist))
		If res = #EVAL_ERROR : ProcedureReturn #SUBR_ERROR : EndIf
		If IS_NIL(res) : Break : EndIf
	ForEver
	ProcedureReturn #T
EndProcedure

;(em)
Procedure F_ElapsedMilliseconds(arglist.i)
	ProcedureReturn MakeNum(ElapsedMilliseconds())
EndProcedure

Procedure F_Progn(arglist.i)	
	Define res.i
	While IS_NOT_NIL(arglist)
		res = eval(car(arglist))
		If res = #EVAL_ERROR : ProcedureReturn #SUBR_ERROR : EndIf
		arglist = cdr(arglist)
	Wend
	ProcedureReturn res
EndProcedure

Procedure F_SetQ(arglist.i)
	Define arg1.i, arg2.i
	If CheckArgs(#TEST_LEN2, "setq", arglist) = #CHECK_ERROR Or CheckArgs(#TEST_SYMBOL, "setq", car(arglist)) = #CHECK_ERROR
		ProcedureReturn #SUBR_ERROR
	EndIf
	arg1 = car(arglist)
	arg2 = eval(cadr(arglist))
	If arg2 = #EVAL_ERROR
		ProcedureReturn #SUBR_ERROR
	EndIf
	BindSym(arg1, arg2)
	ProcedureReturn arg2
EndProcedure

Procedure F_Car(arglist.i)
	If CheckArgs(#TEST_LEN1, "car", arglist) = #CHECK_ERROR : ProcedureReturn #SUBR_ERROR : EndIf
	Define arg1.i = car(arglist)
	ProcedureReturn car(arg1)
EndProcedure

Procedure F_Cdr(arglist.i)
	If CheckArgs(#TEST_LEN1, "cdr", arglist) = #CHECK_ERROR : ProcedureReturn #SUBR_ERROR : EndIf
	Define arg1.i = car(arglist)
	ProcedureReturn cdr(arg1)
EndProcedure

Procedure F_Cons(arglist.i)
	If CheckArgs(#TEST_LEN2, "cons", arglist) = #CHECK_ERROR : ProcedureReturn #SUBR_ERROR : EndIf
	Define arg1 = car(arglist)
	Define arg2 = cadr(arglist)
	ProcedureReturn cons(arg1, arg2)
EndProcedure

Procedure F_RunFile(arglist.i)
     If CheckArgs(#TEST_LEN1, "load", arglist) = #CHECK_ERROR : ProcedureReturn #SUBR_ERROR : EndIf
     If CheckArgs(#TEST_STRING, "load", car(arglist)) = #CHECK_ERROR : ProcedureReturn #SUBR_ERROR : EndIf
     Define arg = car(arglist)
     Define filename.s = PeekS(GET_NUMBER(arg))
     Define str.s = ""
     If ReadFile(0, Trim(filename, Chr(34)))
          While Eof(0) = #False
               Define tmpstr.s = ReadString(0)
               tmpstr = ReplaceString(tmpstr, #TAB$, "")    ;remove tabs
               str = str + tmpstr          
          Wend
          CloseFile(0)          
          
          current_line = str : current_line_index = 1
          Define r = Read_()
          If r = #READ_ERROR : Goto ErrorExit : EndIf          
          r= Eval(r)
          If r = #EVAL_ERROR : Goto ErrorExit : EndIf
          If r = #READ_ERROR : Goto ErrorExit : EndIf
          ProcedureReturn r

     Else
          ProcedureReturn #nil
     EndIf
     
     ErrorExit:
     ResetInputBuffer()
     ProcedureReturn #nil
EndProcedure

Procedure InitSubr()
	;define built in subroutines
	;defsubr - evaulate arguments
	
	DefSubr(GetNameCode("print"), @F_Print())
	DefSubr(GetNameCode("="), @F_Num_EQ())
	DefSubr(GetNameCode(">"), @F_Num_GT())
	DefSubr(GetNameCode("<"), @F_Num_LT())
	DefSubr(GetNameCode(">="), @F_Num_GE())
	DefSubr(GetNameCode("<="), @F_Num_LE())
	DefSubr(GetNameCode("!="), @F_Num_NE())
	DefSubr(GetNameCode("apply"), @F_Apply())
	DefSubr(GetNameCode("eval"), @F_Eval())
	DefSubr(GetNameCode("+"), @F_Plus())
	DefSubr(GetNameCode("*"), @F_Mul())
	DefSubr(GetNameCode("/"), @F_Div())
	DefSubr(GetNameCode("-"), @F_Minus())
	DefSubr(GetNameCode("%"), @F_Mod())
	DefSubr(GetNameCode("car"), @F_Car())
	DefSubr(GetNameCode("cdr"), @F_Cdr())
	DefSubr(GetNameCode("cons"), @F_Cons())
	DefSubr(GetNameCode("load"), @F_RunFile())
	
	;deffsubr - do not evaluate arguments
	DefFSubr(GetNameCode("defun"), @F_Defun())
	DefFSubr(GetNameCode("progn"), @F_Progn())
	DefFSubr(GetNameCode("setq"), @F_SetQ())
	DefFSubr(GetNameCode("while"), @F_While())
	DefFSubr(GetNameCode("em"), @F_ElapsedMilliseconds())
	DefFSubr(GetNameCode("cond"), @F_Cond())
	DefFSubr(GetNameCode("if"), @F_If())
	DefFSubr(GetNameCode("newline"), @F_NewLine())
EndProcedure

Procedure ResetInputBuffer()
	current_line_index = 1
	current_line = ""
EndProcedure

Procedure Main()
	OpenConsole()
	InitCell()
	InitSubr()
	Define ret = 0
	repl:
	
	If ret = 0
		Repeat 
			Print_("> ",0)
			current_line = Input() : current_line_index = 1
			Define r = Read_()
			
			If r = #READ_ERROR : ret = 1 : Goto repl : EndIf
			r = Eval(r)
			If r = #EVAL_ERROR : ret = 1 : Goto repl : EndIf
			If r = #READ_ERROR : ret = 1 : Goto repl : EndIf
			PrintS(r)
			Print_("")
		ForEver
	Else
		If ret = 1
			ResetInputBuffer()
			ret = 0
			Goto repl
		Else
			ProcedureReturn 0
		EndIf
	EndIf
EndProcedure
Main()
