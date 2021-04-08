" Vim filetype plugin file
" Language:	Verilog HDL + SystemVerilog HDL
" Maintainer:	Chih-Tsun Huang <cthuang@larc.ee.nthu.edu.tw>
" Modified : TG
" Last Change:	Thu Dec  6 19:49:51 CET 2012
" Original URL:		http://larc.ee.nthu.edu.tw/~cthuang/vim/ftplugin/verilog.vim

" Only do this when not done yet for this buffer
if exists("b:did_ftplugin")
  finish
endif

" Define include string
setlocal include=^\\s*`include

" Configure syntastic which only recognizes verilog filetype
let g:syntastic_filetype_map = {"systemverilog":"verilog"}
au FileType systemverilog let g:syntastic_verilog_compiler_options = '-Wall --default-language "1800-2012"'

" ALE conf
au FileType systemverilog let b:ale_linters = { 'systemverilog' :  ['verilator'], }
au FileType systemverilog let b:ale_verilog_verilator_options = '-sv --default-language "1800-2012"'
au FileType verilog let b:ale_linters = { 'verilog' :  ['verilator'], }
au FileType verilog let b:ale_verilog_verilator_options = '--default-language "1364-2005"'

" SystemVerilog for keywords tagbar
" Tested with Universal Ctags (https://ctags.io/)
let g:tagbar_type_systemverilog = {
    \ 'ctagstype': 'systemverilog',
    \ 'kinds' : [
         \'A:assertions',
         \'C:classes',
         \'E:enumerators',
         \'H:checkers',
         \'I:interfaces',
         \'K:packages',
         \'L:clockings',
         \'M:modports',
         \'N:nettype declarations',
         \'O:contraints',
         \'P:programs',
         \'Q:prototypes',
         \'R:properties',
         \'S:structs and unions',
         \'T:type declarations',
         \'V:covergroups',
         \'b:blocks',
         \'c:constants',
         \'e:events',
         \'f:functions',
         \'i:instances',
         \'l:interface class',
         \'m:modules',
         \'n:net data types',
         \'p:ports',
         \'q:sequences',
         \'r:register data types',
         \'t:tasks',
         \'w:structs and unions members',
     \],
     \ 'sro': '.',
     \ 'kind2scope' : {
        \ 'K' : 'package',
        \ 'C' : 'class',
        \ 'm' : 'module',
        \ 'P' : 'program',
        \ 'I' : 'interface',
        \ 'M' : 'modport',
        \ 'f' : 'function',
        \ 't' : 'task',
        \ 'V' : 'covergroup',
     \},
     \ 'scope2kind' : {
        \ 'package'   : 'K',
        \ 'class'     : 'C',
        \ 'module'    : 'm',
        \ 'program'   : 'P',
        \ 'interface' : 'I',
        \ 'modport'   : 'M',
        \ 'function'  : 'f',
        \ 'task'      : 't',
     \ },
     \}

" Don't load another plugin for this buffer
let b:did_ftplugin = 1

" Set 'cpoptions' to allow line continuations
let s:cpo_save = &cpo
set cpo&vim

" Undo the plugin effect
let b:undo_ftplugin = "setlocal fo< com< tw<"
    \ . "| unlet! b:browsefilter b:match_ignorecase b:match_words"

" Set 'formatoptions' to break comment lines but not other lines,
" and insert the comment leader when hitting <CR> or using "o".
setlocal fo-=t fo+=croqlm1

" Set 'comments' to format dashed lists in comments.
setlocal comments=sO:*\ -,mO:*\ \ ,exO:*/,s1:/*,mb:*,ex:*/,://

" Win32 can filter files in the browse dialog
if has("gui_win32") && !exists("b:browsefilter")
  let b:browsefilter = "Verilog Source Files (*.v)\t*.v\n" .
	\ "All Files (*.*)\t*.*\n"
endif

" Let the matchit plugin know what items can be matched.
if exists("loaded_matchit")
  let b:match_ignorecase=0
  let b:match_words=
  \ '\<begin\>:\<end\>,' .
  \ '\<if\>:\<else\>,' .
  \ '\<module\>:\<endmodule\>,' .
  \ '\<class\>:\<endclass\>,' .
  \ '\<checker\>:\<endchecker\>,' .
  \ '\<program\>:\<endprogram\>,' .
  \ '\<clocking\>:\<endclocking\>,' .
  \ '\<property\>:\<endproperty\>,' .
  \ '\<sequence\>:\<endsequence\>,' .
  \ '\<package\>:\<endpackage\>,' .
  \ '\<covergroup\>:\<endgroup\>,' .
  \ '\<primitive\>:\<endprimitive\>,' .
  \ '\<config\>:\<endconfig\>,' .
  \ '\<specify\>:\<endspecify\>,' .
  \ '\<generate\>:\<endgenerate\>,' .
  \ '\<interface\>:\<endinterface\>,' .
  \ '\<function\>:\<endfunction\>,' .
  \ '\<task\>:\<endtask\>,' .
  \ '\<case\>\|\<casex\>\|\<casez\>:\<endcase\>,' .
  \ '\<fork\>:\<join\>\|\<join_any\>\|\<join_none\>,' .
  \ '`if\(n\)\?def\>:`elsif\>:`else\>:`endif\>,' .
  \ '\<generate\>:\<endgenerate\>,' .
  \ '\<covergroup\>:\<endgroup\>,'
endif

" Reset 'cpoptions' back to the user's setting
let &cpo = s:cpo_save
unlet s:cpo_save
