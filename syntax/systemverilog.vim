" Vim syntax file
" Language:	System_Verilog
" Maintainer:	T.G.
" Last Update:  Thu Apr  2 14:28:24 CEST 2009

" For version 5.x: Clear all syntax items
" For version 6.x: Quit when a syntax file was already loaded
if version < 600
   syntax clear
elseif exists("b:current_syntax")
   finish
endif

" Set the local value of the 'iskeyword' option
if version >= 600
   setlocal iskeyword=@,48-57,_,192-255
else
   set iskeyword=@,48-57,_,192-255
endif

" A bunch of useful SVerilog keywords

syn keyword SverilogType        shortint int longint byte bit logic integer
syn keyword SverilogType        reg input output inout realtime signed unsigned
syn keyword SverilogType        time wire real shortreal chandle string event
syn keyword SverilogType        enum struct union rand randc mailbox
syn keyword SverilogType        supply0 supply1 tri tri0 tri1 triand trior trireg
syn keyword SverilogType        strong0 strong1 pull0 pull1 weak0 weak1 wand wor

syn keyword SverilogStatement   alias always always_comb always_ff always_latch
syn keyword SverilogStatement   and assert assert_strobe assign automatic
syn keyword SverilogStatement   before bind break buf bufif0 bufif1
syn keyword SverilogStatement   cell clocking cmos config class endclass
syn keyword SverilogStatement   const constraint context continue cover
syn keyword SverilogStatement   deassign defparam design disable dist do
syn keyword SverilogStatement   edge endconfig endclocking
syn keyword SverilogStatement   endinterface endfunction endmodule
syn keyword SverilogStatement   endprimitive endspecify endtable endtask
syn keyword SverilogStatement   endpackage endprogram endproperty endsequence
syn keyword SverilogStatement   export extends implements extern final first_match
syn keyword SverilogStatement   force function
syn keyword SverilogStatement   genvar highz0 highz1 ifnone
syn keyword SverilogStatement   incdir include initial
syn keyword SverilogStatement   iff import inside interface intersect
syn keyword SverilogStatement   instance large liblist
syn keyword SverilogStatement   library localparam macromodule medium
syn keyword SverilogStatement   local modport new null packed
syn keyword SverilogStatement   module nand negedge nmos nor
syn keyword SverilogStatement   noshowcancelled not notif0 notif1 or
syn keyword SverilogStatement   package parameter pmos posedge primitive
syn keyword SverilogStatement   pulldown pullup
syn keyword SverilogStatement   pulsestyle_onevent pulsestyle_ondetect
syn keyword SverilogStatement   priority program property protected pure
syn keyword SverilogStatement   rcmos release
syn keyword SverilogStatement   rnmos rpmos rtran rtranif0 rtranif1
syn keyword SverilogStatement   return ref sequence
syn keyword SverilogStatement   scalared showcancelled small
syn keyword SverilogStatement   specify specparam 
syn keyword SverilogStatement   solve static super
syn keyword SverilogStatement   table task tran
syn keyword SverilogStatement   tranif0 tranif1
syn keyword SverilogStatement   use vectored wait
syn keyword SverilogStatement   this throughout timeprecision timeunit
syn keyword SverilogStatement   type typedef unique0 unique var virtual
syn keyword SverilogStatement   void wait_order with within
syn keyword SverilogStatement   xnor xor
syn keyword SverilogLabel       begin end fork join join_any  join_none
syn keyword SverilogConditional if else case casex casez default endcase
syn keyword SverilogRepeat      forever repeat while for foreach

"To make generate statement more visible
syn keyword SverilogGenerate generate endgenerate

syn keyword SverilogTodo contained TODO

syn match   SverilogOperator "[&|~><!)(*#%@+/=?:;}{,.\^\-\[\]]"

syn region  SverilogComment start="/\*" end="\*/" contains=SverilogTodo,@Spell
syn match   SverilogComment "//.*" contains=SverilogTodo,@Spell

syn match SverilogMacro  "`\(\K\k*\)*\>"
syn match SverilogGlobal "`celldefine"
syn match SverilogGlobal "`default_nettype"
syn match SverilogGlobal "`define"
syn match SverilogGlobal "`else"
syn match SverilogGlobal "`elsif"
syn match SverilogGlobal "`endcelldefine"
syn match SverilogGlobal "`endif"
syn match SverilogGlobal "`ifdef"
syn match SverilogGlobal "`ifndef"
syn match SverilogGlobal "`include"
syn match SverilogGlobal "`line"
syn match SverilogGlobal "`nounconnected_drive"
syn match SverilogGlobal "`resetall"
syn match SverilogGlobal "`timescale"
syn match SverilogGlobal "`unconnected_drive"
syn match SverilogGlobal "`undef"
syn match SverilogGlobal "`__FILE__"
syn match SverilogGlobal "`__LINE__"

syn match   SverilogConstant "\<[A-Z][A-Z0-9_]\+\>"

syn match   SverilogNumber "\(\<\d\+\|\)'[sS]\?\s*[bB]\s*[0-1_xXzZ?]\+\>"
syn match   SverilogNumber "\(\<\d\+\|\)'[sS]\?\s*[oO]\s*[0-7_xXzZ?]\+\>"
syn match   SverilogNumber "\(\<\d\+\|\)'[sS]\?\s*[dD]\s*[0-9_xXzZ?]\+\>"
syn match   SverilogNumber "\(\<\d\+\|\)'[sS]\?\s*[hH]\s*[0-9a-fA-F_xXzZ?]\+\>"
syn match   SverilogNumber "\<[+-]\=[0-9_]\+\(\.[0-9_]*\|\)\(e[0-9_]*\|\)\>"
syn match   SverilogNumber "\(\)'[0-1xXzZ]\>"

syn match   SverilogTime   "\<[0-9]*\.*[0-9]\+\s*\(ps\|ns\|us\|ms\|s\)\>"

syn region  SverilogString start=+"+ skip=+\\"+ end=+"+ contains=SverilogEscape,@Spell
syn match   SverilogEscape +\\[nt"\\]+ contained
syn match   SverilogEscape "\\\o\o\=\o\=" contained

" Directives
syn match   SverilogDirective   "//\s*synopsys\>.*$"
syn match   SverilogDirective   "//\s*synthesis\>.*$"
syn match   SverilogDirective   "//\s*pragma\>.*$"
syn region  SverilogDirective   start="/\*\s*synopsys\>" end="\*/"
syn region  SverilogDirective   start="//\s*synopsys dc_script_begin\>" end="//\s*synopsys dc_script_end\>"

" Verilog2001 attributes
syn region  SverilogDirective   start="(\*[^)]" end="\*)"

syn match   SverilogDirective   "//\s*\$s\>.*$"
syn region  SverilogDirective   start="/\*\s*\$s\>" end="\*/"
syn region  SverilogDirective   start="//\s*\$s dc_script_begin\>" end="//\s*\$s dc_script_end\>"

" system tastks and functions $stop/$print...
syn match SverilogFunction "\$[a-zA-Z0-9_]\+\>"

"syn match  SverilogMethod       "\.atobin\>"
"syn match  SverilogMethod       "\.atohex\>"
"syn match  SverilogMethod       "\.atoi\>"
"syn match  SverilogMethod       "\.atooct\>"
"syn match  SverilogMethod       "\.atoreal\>"
"syn match  SverilogMethod       "\.bintoa\>"
"syn match  SverilogMethod       "\.hextoa\>"
"syn match  SverilogMethod       "\.itoa\>"
"syn match  SverilogMethod       "\.octtoa\>"
"syn match  SverilogMethod       "\.realtoa\>"
"syn match  SverilogMethod       "\.len\>"
"syn match  SverilogMethod       "\.getc\>"
"syn match  SverilogMethod       "\.putc\>"
"syn match  SverilogMethod       "\.toupper\>"
"syn match  SverilogMethod       "\.tolower\>"
"syn match  SverilogMethod       "\.compare\>"
"syn match  SverilogMethod       "\.icompare\>"
"syn match  SverilogMethod       "\.substr\>"
"syn match  SverilogMethod       "\.num\>"
"syn match  SverilogMethod       "\.exists\>"
"syn match  SverilogMethod       "\.first\>"
"syn match  SverilogMethod       "\.last\>"
"syn match  SverilogMethod       "\.name\>"
"syn match  SverilogMethod       "\.index\>"
"syn match  SverilogMethod       "\.find\>"
"syn match  SverilogMethod       "\.find_first\>"
"syn match  SverilogMethod       "\.find_last\>"
"syn match  SverilogMethod       "\.find_index\>"
"syn match  SverilogMethod       "\.find_first_index\>"
"syn match  SverilogMethod       "\.find_last_index\>"
"syn match  SverilogMethod       "\.min\>"
"syn match  SverilogMethod       "\.max\>"
"syn match  SverilogMethod       "\.unique\>"
"syn match  SverilogMethod       "\.unique_index\>"
"syn match  SverilogMethod       "\.sort\>"
"syn match  SverilogMethod       "\.rsort\>"
"syn match  SverilogMethod       "\.shuffle\>"
"syn match  SverilogMethod       "\.reverse\>"
"syn match  SverilogMethod       "\.sum\>"
"syn match  SverilogMethod       "\.product\>"
"syn match  SverilogMethod       "\.xor\>"
"syn match  SverilogMethod       "\.status\>"
"syn match  SverilogMethod       "\.kill\>"
"syn match  SverilogMethod       "\.self\>"
"syn match  SverilogMethod       "\.await\>"
"syn match  SverilogMethod       "\.suspend\>"
"syn match  SverilogMethod       "\.resume\>"
"syn match  SverilogMethod       "\.get\>"
"syn match  SverilogMethod       "\.put\>"
"syn match  SverilogMethod       "\.peek\>"
"syn match  SverilogMethod       "\.try_get\>"
"syn match  SverilogMethod       "\.try_peek\>"
"syn match  SverilogMethod       "\.try_put\>"
"syn match  SverilogMethod       "\.data\>"
"syn match  SverilogMethod       "\.eq\>"
"syn match  SverilogMethod       "\.neq\>"
"syn match  SverilogMethod       "\.next\>"
"syn match  SverilogMethod       "\.prev\>"
"syn match  SverilogMethod       "\.new\>"
"syn match  SverilogMethod       "\.size\>"
"syn match  SverilogMethod       "\.delete\>"
"syn match  SverilogMethod       "\.empty\>"
"syn match  SverilogMethod       "\.pop_front\>"
"syn match  SverilogMethod       "\.pop_back\>"
"syn match  SverilogMethod       "\.push_front\>"
"syn match  SverilogMethod       "\.push_back\>"
"syn match  SverilogMethod       "\.front\>"
"syn match  SverilogMethod       "\.back\>"
"syn match  SverilogMethod       "\.insert\>"
"syn match  SverilogMethod       "\.insert_range\>"
"syn match  SverilogMethod       "\.erase\>"
"syn match  SverilogMethod       "\.erase_range\>"
"syn match  SverilogMethod       "\.set\>"
"syn match  SverilogMethod       "\.swap\>"
"syn match  SverilogMethod       "\.clear\>"
"syn match  SverilogMethod       "\.purge\>"
"syn match  SverilogMethod       "\.start\>"
"syn match  SverilogMethod       "\.finish\>"

"Modify the following as needed.  The trade-off is performance versus
"functionality.
syn sync minlines=50

" Define the default highlighting.
" For version 5.7 and earlier: only when not done already
" For version 5.8 and later: only when an item doesn't have highlighting yet
if version >= 508 || !exists("did_Sverilog_syn_inits")
   if version < 508
      let did_Sverilog_syn_inits = 1
      command -nargs=+ HiLink hi link <args>
   else
      command -nargs=+ HiLink hi def link <args>
   endif

   " The default highlighting.
   HiLink SverilogCharacter         Character
   HiLink SverilogConditional       Conditional
   HiLink SverilogRepeat            Repeat
   HiLink SverilogString            String
   HiLink SverilogTodo              Todo
   HiLink SverilogDirective         SpecialComment
   HiLink SverilogComment           Comment
   HiLink SverilogConstant          Constant
   HiLink SverilogLabel             Label
   HiLink SverilogNumber            Number
   HiLink SverilogOperator          Special
   HiLink SverilogStatement         Statement
   HiLink SverilogGlobal            Define
   HiLink SverilogEscape            Special
   HiLink SverilogType              Type
   HiLink SverilogFunction          Function
   HiLink SverilogMethod            Function
   HiLink SverilogGenerate          Constant
   HiLink SverilogTime              Special
   HiLink SverilogMacro             none

   delcommand HiLink
endif

let b:current_syntax = "systemverilog"

" vim: ts=8
