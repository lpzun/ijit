/*******************************************************************************
 ** Name:    	BoPP: parser
 ** Authors: 	Peizun Liu
 ** Version: 	0.5
 ** Copyright: 	It belongs to Thomas Wahl's group in CAR Lab, CCIS, NEU
 ** Create on:  Feb, 2014
 ** Modified :  Jan, 2016
 ** Decription: BoPP is a Boolean Program Parser written with C++. It aims  at
 *		parsing Boolean programs to generate a control folow graph and 
 *		the corresponding weakest preconditions (strongest postcondit-
 *              ions) for each statement when computing a preimage (postimage).
 *
 *              parser: 
 *              v0.5: adding the forward-based CFG and so on
 ******************************************************************************/
%language "C++"
%locations     // enable location tracking
%error-verbose // verbose error messages

%code requires
{
# include "aide.hh"
  using namespace iotf;
}

 // tell Bison that yyparse should take an extra parameter paide
%parse-param { fw_aide &aide }

%define parser_class_name {bp} // define the parser's name
%{
%}

// use Bison's %union construct to define a semantic value type for integers 
// and character pointers (strings)
%union {
  int   t_val; // token's value
  char *t_str; // token's name
}

/* declare tokens */
%token T_BEGIN "begin"
%token T_END "end"

%token T_DECL "decl"
%token T_GOTO "goto"
%token T_ASSUME "assume"
%token T_SKIP "skip"
%token T_ASSERT "assert"
%token T_IF "if"
%token T_FI "fi"
%token T_THEN "then"
%token T_VOID "void"
%token T_CSTR "constrain"
%token T_START_THREAD "start_thread"
%token T_END_THREAD "end_thread"
%token T_ATOMIC_BEGIN "atomic_begin"
%token T_ATOMIC_END "atomic_end"
%token T_WAIT "wait"
%token T_BROADCAST "broadcast"

%token T_NONDET "*"
%token T_ASSIGN ":="
%token T_EQ_OP "="
%token T_NE_OP "!="
%token T_AND   "&&"
%token T_OR    "||"
%token T_TERNARY "?"


%token <t_val> T_INT
%token <t_str> T_IDEN

%type <t_str> prm_expr una_expr equ_expr and_expr xor_expr or_expr expr // value
%type <t_str> to_line_list// metastmt statement labelstmt declstmt stmt stmtlist

%start prog
%{
  extern int yylex(yy::bp::semantic_type *yylval, yy::bp::location_type* yylloc);
%}

%initial-action {
  // add filename to location info here
  @$.begin.filename = @$.end.filename = new std::string("stdin");
 }


/*******************************************************************************
 * ** bison rules for BoPP parser 
 * ** BNF: prog
 *	    |-s_decllist 
 *	    |-funclist
 * 	      |-function
 *              |-funchead
 *              |-funcbody
 * 	          |-funcstmt
 * 	             |-l_declstmt
 * 	             |-initstmt
 * 	             |-labelstmt
 * 	               |-expr
 *               |-funcend
 ******************************************************************************/
%%
prog: s_decllist funclist
| funclist
;

funclist: function
| funclist function
;

function: funchead funcbody funcend;

funchead: T_VOID T_IDEN '(' ')' T_BEGIN;

funcend: T_END;

funcbody: funcstmt
| funcbody funcstmt
;

funcstmt: l_declstmt
| initistmt
| labelstmt
;

/// shared variables decls
s_decllist: s_declstmt
| s_decllist s_declstmt
;

s_declstmt: T_DECL s_id_list ';'
;

s_id_list: s_id
| s_id_list ',' s_id
;

s_id: T_IDEN {
  aide.s_vars_list.emplace($1, ++aide.s_vars_num);
  aide.s_vars_init[aide.s_vars_num] = '*';
  free($1); // free it to avoid storage leaks
 }
| T_IDEN T_ASSIGN T_NONDET {
  aide.s_vars_list.emplace($1, ++aide.s_vars_num);
  aide.s_vars_init[aide.s_vars_num] = '*';
  free($1); // free it to avoid storage leaks
 }
| T_IDEN T_ASSIGN T_INT {
  aide.s_vars_list.emplace($1, ++aide.s_vars_num);
  aide.s_vars_init[aide.s_vars_num] = ($3 == 0 ? '0' : '1');
  free($1); // free it to avoid storage leaks
 }
;

/* local decls */
l_declstmt: T_DECL l_id_list ';' { }
;

l_id_list: l_id
| l_id_list ',' l_id {}
;

l_id: T_IDEN {
  aide.l_vars_list.emplace($1, ++aide.l_vars_num);
  aide.l_vars_init[aide.l_vars_num] = '*';
  free($1);
 }
| T_IDEN T_ASSIGN T_NONDET {
  aide.l_vars_list.emplace($1, ++aide.l_vars_num);
  aide.l_vars_init[aide.l_vars_num] = '*';
  free($1);
 }
| T_IDEN T_ASSIGN T_INT {
  aide.l_vars_list.emplace($1, ++aide.l_vars_num);
  aide.l_vars_init[aide.l_vars_num] = ($3 == 0 ? '0' : '1');
  free($1);
 }
;

///////////// stmts /////////////////
/// initialization
initistmt: T_IDEN T_ASSIGN T_NONDET ';' {
  aide.add_vars_init($1, 2);
  free($1);
 }
|T_IDEN T_ASSIGN T_INT ';' {
  aide.add_vars_init($1, $3);
  free($1);
 }
;
/// labeling statement
labelstmt: T_INT { 
  ++aide.lineno; // counting the program counters
  aide.ipc = (int)($1); // obtain current pc
  if(!aide.is_pc_unique($1)) // pc's uniqueness
    YYABORT; 
 } ':' statement {
   cout << "TEST:: I am in statement " << $1 <<endl;
   }
;

statement: metastmt
| statement T_AND metastmt // multi-statements
| statement T_OR metastmt
;

metastmt: T_SKIP ';' { // "skip" statement
  aide.add_edge(aide.ipc, aide.ipc+1, aide.create_skip_stmt_sp());	
  }
| T_GOTO {} to_line_list ';' { // "goto" statement
  aide.add_edge(aide.ipc, aide.create_goto_stmt_sp());
  aide.succ_pc_set.clear();
  }
| iden_list T_ASSIGN expr_list ';' {// "parallel assignment" statement
  aide.add_edge(aide.ipc, aide.ipc+1, aide.create_assg_stmt_sp(aide.ipc));	
  // reset containers
  aide.assign_stmt_lhs.clear();
  aide.assign_stmt_rhs.clear();
 }
| iden_list T_ASSIGN expr_list T_CSTR expr ';' {// "PA with constrain"  
  string e = aide.recov_expr_from_list(aide.expr_in_list, true);
  aide.expr_in_list.clear();
  aide.add_edge(aide.ipc, aide.ipc+1, aide._AND_ + "(" + e + ")");
  // reset containers
  aide.assign_stmt_lhs.clear();
  aide.assign_stmt_rhs.clear();
 }
| T_IF expr T_THEN metastmt T_FI ';' { // "if...then..." statement
  string e = aide.recov_expr_from_list(aide.expr_in_list, true);
  aide.create_ifth_stmt_sp(e);
  aide.add_edge(aide.ipc, aide.ipc+1, aide.create_else_stmt_sp(e));
  aide.expr_in_list.clear();
 } 
| T_ASSERT '(' expr ')' ';' { // "assert" statement
  aide.add_edge(aide.ipc, aide.ipc+1, aide.create_asse_stmt_sp());		
  aide.all_sat_solver(aide.expr_in_list, aide.ipc);
  aide.expr_in_list.clear();
  }
| T_ASSUME '(' expr ')' ';' { // "assume" statement
  aide.add_edge(aide.ipc, aide.ipc+1, aide.create_assu_stmt_sp());
  aide.expr_in_list.clear();
  }
| T_START_THREAD T_GOTO T_INT ';' { // "thread creation" statement
  aide.add_edge(aide.ipc, aide.ipc+1, 
                      aide.create_nthr_stmt_sp(std::to_string($3)));
 }
| T_END_THREAD ';' { // thread termination statement
  aide.add_edge(aide.ipc, aide.ipc+1, aide.create_skip_stmt_sp());
  }
| T_ATOMIC_BEGIN ';' { // atomic section beginning
  aide.add_edge(aide.ipc, aide.ipc+1, aide.create_atom_stmt_sp());
  }
| T_ATOMIC_END ';' { // atomic section ending
  aide.add_edge(aide.ipc, aide.ipc+1, aide.create_eatm_stmt_sp());
  }
| T_BROADCAST ';' { // broadcast statement
  aide.add_edge(aide.ipc, aide.ipc+1, aide.create_bcst_stmt_sp());
  }
| T_WAIT ';' { // wait statement
  aide.add_edge(aide.ipc, aide.ipc+1, aide.create_wait_stmt_sp());
  }
;

iden_list: T_IDEN {
  aide.assign_stmt_lhs.emplace_back($1);
  free($1);
 }
| iden_list ',' T_IDEN {
  aide.assign_stmt_lhs.emplace_back($3);
  free($3); 
  }
;

expr_list: expr { 
  aide.assign_stmt_rhs.emplace_back(aide.expr_in_list); 
  aide.expr_in_list.clear();
 }
| expr_list ',' expr { 
  aide.assign_stmt_rhs.emplace_back(aide.expr_in_list); 
  aide.expr_in_list.clear(); 
  }
;

to_line_list: T_INT  {
  aide.succ_pc_set.emplace($1);
 }
| to_line_list ',' T_INT {
  aide.succ_pc_set.emplace($3);
  }
;

/* expressions */
expr: or_expr { }
| expr T_TERNARY expr ':' or_expr {
  cout<<"This is a ternary expression"<<endl;
 }
;

or_expr: xor_expr
| or_expr T_OR xor_expr { aide.add_to_expr_in_list("|"); }
;

xor_expr: and_expr
| xor_expr '^' and_expr { aide.add_to_expr_in_list("^"); }
;

and_expr: equ_expr
| and_expr T_AND equ_expr { aide.add_to_expr_in_list("&"); }
;

equ_expr: una_expr
| equ_expr T_EQ_OP una_expr { aide.add_to_expr_in_list( "="); }
| equ_expr T_NE_OP una_expr { aide.add_to_expr_in_list("!="); }
;

una_op: '!' 
;

una_expr: prm_expr
| una_op prm_expr { aide.add_to_expr_in_list("!"); }
;

prm_expr: '(' expr ')' { aide.add_to_expr_in_list("()"); }
| T_NONDET { aide.add_to_expr_in_list("*"); }
| T_INT    { aide.add_to_expr_in_list($1 ? "1" : "0"); }
| T_IDEN { 
  string id = $1;
  if(id.at(0) == '\'') // a successor variable
    id = aide.SUCC_POSTFIX + id.substr(1);
    aide.add_to_expr_in_list(id); 
    free($1);
  }
;
%%

/*******************************************************************************
 * ** From here, 
 *         functions used in parser, defined in c++
 *
 *    Mar. 2013
 ******************************************************************************/
namespace yy {
  void bp::error(location const &loc, const std::string& s) {
    std::cerr << "error at " << loc << ": " << s << std::endl;
  }
}
