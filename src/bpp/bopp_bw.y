/*************************************************************************************
 ** Name:    	BoPP: parser
 ** Authors: 	Peizun Liu
 ** Version: 	0.4
 ** Copyright: 	It belongs to Thomas Wahl's group in CAR Lab, CCIS, NEU
 ** Date:       Feb, 2014
 ** Decription: BoPP is a C++ version of Boolean Program Parser. It aims to 
 *		parse Boolean programs and generate its control folow graph 
 *		and the corresponding weakest precondition function for each
 *              statement.
 *
 *              parser: 
 *              
 *              This version is to generate the DIMACS CNF format of WP, which
 *              can be used in (most) SAT solver directly
 ************************************************************************************/
%language "C++"
%defines
%locations

%define parser_class_name "bw" // define the parser's name
%{
%}

%union {
  int t_val; // token's value
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

%type <t_str> prm_expr una_expr equ_expr and_expr xor_expr or_expr expr //value
%type <t_str> to_line_list //metastmt statement labelstmt declstmt stmt stmtlist

%start prog

%{
#include "bopp.hh"
  using namespace iotf;
  bw_aide aide;

  extern int yylex(yy::bw::semantic_type *yylval, yy::bw::location_type* yylloc);
%}

%initial-action {
  // add filename to location info here
  @$.begin.filename = @$.end.filename = new std::string("stdin");
 }


/*************************************************************************************
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
 ************************************************************************************/
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
| labelstmt { aide.lineno++; }
;

/* shared decls */
s_decllist: s_declstmt
| s_decllist s_declstmt
;

s_declstmt: T_DECL s_id_list ';' { }
;

s_id_list: s_id
| s_id_list ',' s_id {}
;

s_id: T_IDEN {
  if(aide.add_to_shared_vars_list($1, ++aide.s_vars_num)) {
    aide.s_var_init[aide.s_vars_num]='*';
  }
  free($1); // free it to avoid storage leaks
 }
| T_IDEN T_ASSIGN T_NONDET {
  if(aide.add_to_shared_vars_list($1, ++aide.s_vars_num)) {
    aide.s_var_init[aide.s_vars_num] = '*';
  }
  free($1);
 }
| T_IDEN T_ASSIGN T_INT {
  if(aide.add_to_shared_vars_list($1, ++aide.s_vars_num)) {
    aide.s_var_init[aide.s_vars_num] = ($3 == 0 ? '0' : '1');
  }
  free($1);
 }
;

/* local decls */
l_declstmt: T_DECL l_id_list ';' { }
;

l_id_list: l_id
| l_id_list ',' l_id {}
;

l_id: T_IDEN {
  if(aide.add_to_local_vars_list($1, ++aide.l_vars_num)) {
    aide.l_var_init[aide.l_vars_num] = '*';
  }
  free($1);
 }
| T_IDEN T_ASSIGN T_NONDET {
  if(aide.add_to_local_vars_list($1, ++aide.l_vars_num)) {
    aide.l_var_init[aide.l_vars_num] = '*';
  }
  free($1);
 }
| T_IDEN T_ASSIGN T_INT {
  if(aide.add_to_local_vars_list($1, ++aide.l_vars_num)) {
    aide.l_var_init[aide.l_vars_num] = ($3 == 0 ? '0' : '1');
  }
  free($1);
 }
;

/* stmts */
initistmt: T_IDEN T_ASSIGN T_NONDET ';' {
  map<string, ushort>::iterator ifind;
  if ((ifind = aide.s_vars_list.find($1)) != aide.s_vars_list.end()) {
    aide.s_var_init[ifind->second] = '*';
  }
  if ((ifind = aide.l_vars_list.find($1)) != aide.l_vars_list.end()) {
    aide.l_var_init[ifind->second] = '*';
  }
  free($1);
 }
|T_IDEN T_ASSIGN T_INT ';' {
  map<string, ushort>::iterator ifind;
  if ((ifind = aide.s_vars_list.find($1)) != aide.s_vars_list.end()) {
    aide.s_var_init[ifind->second] = ($3 == 0 ? '0' : '1');
  }
  if ((ifind = aide.l_vars_list.find($1)) != aide.l_vars_list.end()) {
    aide.l_var_init[ifind->second] = ($3 == 0 ? '0' : '1');
  }
  free($1);
 }
;

labelstmt: T_INT { 
  aide.ipc = (int)($1); 
  if(!aide.is_pc_unique($1)) { // pc's uniqueness
    YYABORT; }
 } ':' statement {
   cout<<"TEST:: I am in statement "<<$1<<endl;									      
   }
;

statement: metastmt
| statement T_AND metastmt // multi-statements
| statement T_OR metastmt
;

metastmt: T_SKIP ';' { // "skip" statement
  aide.add_edge(aide.ipc, aide.ipc+1, aide.create_skip_stmt_wp());	
 }
| T_GOTO {} to_line_list ';' { // "goto" statement
  aide.add_edge(aide.ipc, aide.create_goto_stmt_wp());
  aide.succ_stmt_label.clear();
  aide.goto_targets = "";
  }
| iden_list T_ASSIGN expr_list ';' { // "assignment" statement
  aide.add_edge(aide.ipc, aide.ipc+1, aide.create_assg_stmt_wp());	
  // clear containers
  aide.assign_stmt_lhs.clear();
  aide.assign_stmt_rhs.clear();
 }
| iden_list T_ASSIGN expr_list T_CSTR expr ';' { // "assignment constrain"  
  string e = aide.recov_expr_from_symb_list(aide.expr_symb_list, true);
  aide.expr_symb_list.clear();

  aide.add_edge(aide.ipc, aide.ipc+1, 
       aide.create_assg_stmt_wp() + aide._AND_ + "(" + e + ")");
  // clear containers
  aide.assign_stmt_lhs.clear();
  aide.assign_stmt_rhs.clear();
 }
| T_IF expr T_THEN metastmt T_FI ';' { // "if..then.." statement
  string e = aide.recov_expr_from_symb_list(aide.expr_symb_list, true);
  aide.create_ifth_stmt_wp(e);
  aide.add_edge(aide.ipc, aide.ipc+1, aide.create_else_stmt_wp(e));
  aide.expr_symb_list.clear();
 }
| T_ASSERT '(' expr ')' ';' { // "assert" statement
  aide.add_edge(aide.ipc, aide.ipc+1, aide.create_asse_stmt_wp());		
  aide.exhaustive_sat_solver(aide.expr_symb_list, aide.ipc);
  aide.expr_symb_list.clear();
  }
| T_ASSUME '(' expr ')' ';' { // "assume" statement
  aide.add_edge(aide.ipc, aide.ipc+1, aide.create_assu_stmt_wp());
  aide.expr_symb_list.clear();
  } 
| T_START_THREAD T_GOTO T_INT ';' {
  aide.add_edge(aide.ipc, aide.ipc + 1, aide.create_nthr_stmt_wp(std::to_string($3)));
 }
| T_END_THREAD ';' {
  aide.add_edge(aide.ipc, aide.ipc + 1, aide.create_skip_stmt_wp());
  }
| T_ATOMIC_BEGIN ';' {
  aide.add_edge(aide.ipc, aide.ipc + 1, aide.create_atom_stmt_wp());
  }
| T_ATOMIC_END ';' {
  aide.add_edge(aide.ipc, aide.ipc + 1, aide.create_eatm_stmt_wp());
  }
| T_WAIT ';' {
  aide.add_edge(aide.ipc, aide.ipc + 1, aide.create_wait_stmt_wp());
  }
| T_BROADCAST ';' {
  aide.add_edge(aide.ipc, aide.ipc + 1, aide.create_bcst_stmt_wp());
  }
;

iden_list: T_IDEN {
  aide.assign_stmt_lhs.push_back($1);
  free($1);
 }
| iden_list ',' T_IDEN {
  aide.assign_stmt_lhs.push_back($3);
  free($3); 
  }
;

expr_list: expr { 
  aide.assign_stmt_rhs.push_back(aide.expr_symb_list); 
  aide.expr_symb_list.clear();
 }
| expr_list ',' expr { 
  aide.assign_stmt_rhs.push_back(aide.expr_symb_list); 
  aide.expr_symb_list.clear(); 
  }
;

to_line_list: T_INT  {
  aide.succ_stmt_label.emplace($1);
  aide.goto_targets = aide.goto_targets + "," + std::to_string($1);
 }
| to_line_list ',' T_INT {
  aide.succ_stmt_label.emplace($3);
  aide.goto_targets = aide.goto_targets + "," + std::to_string($3);
  }
;

/* expressions */
expr: or_expr { }
| expr T_TERNARY expr ':' or_expr {
  cout << "This is a ternary expression" << endl;
 }
;

or_expr: xor_expr
| or_expr T_OR xor_expr { aide.add_to_expr_symb_list("||"); }
;

xor_expr: and_expr
| xor_expr '^' and_expr { aide.add_to_expr_symb_list("^"); }
;

and_expr: equ_expr
| and_expr T_AND equ_expr { aide.add_to_expr_symb_list("&&"); }
;

equ_expr: una_expr
| equ_expr T_EQ_OP una_expr { aide.add_to_expr_symb_list("=="); }
| equ_expr T_NE_OP una_expr { aide.add_to_expr_symb_list("!="); }
;

una_op: '!' 
;

una_expr: prm_expr
| una_op prm_expr { aide.add_to_expr_symb_list("!");}
;

prm_expr: '(' expr ')' { aide.add_to_expr_symb_list("()"); }
| T_NONDET { aide.add_to_expr_symb_list("*"); }
| T_INT { aide.add_to_expr_symb_list($1 ? "1" : "0"); }
| T_IDEN { 
  string id = $1;
  if(id.at(0) == '\'') // a successor variable
    id = aide.SUCC_POSTFIX + id.substr(1);
    aide.add_to_expr_symb_list(id); 
    free($1); 
  }
;
%%

  /*************************************************************************************
   * ** From here, 
   *         functions used in parser, defined in c++
   *
   *    Mar. 2013
   ************************************************************************************/
namespace yy {
  void bw::error(location const &loc, const std::string& s) {
    std::cerr << "error at " << loc << ": " << s << std::endl;
  }
}

/***************** Main Function: C++ Code Section of Parser ************************/
/**
 * @brief get a command
 * @param begin
 * @param end
 * @param option
 * @return a cmd
 */
char* getCmdOption(char ** begin, char ** end, const std::string & option) {
  char ** itr = std::find(begin, end, option);
  if (itr != end && ++itr != end) {
    return *itr;
  }
  return 0;
}

/**
 * @brief if a specific cmd exists or not
 * @param begin
 * @param end
 * @param option
 * @return true if exists
 *         false otherwise
 */
bool cmdOptionExists(char** begin, char** end, const std::string& option) {
  return std::find(begin, end, option) != end;
}

int main(int argc, char *argv[]) {
    char DEFAULT_CFG_FILE_NAME[100] = "bp.cfg";
    char DEFAULT_TAF_FILE_NAME[100] = "bp.taf";
    
  if (cmdOptionExists(argv, argv + argc, "-h")) {
    printf("Usage: BoPP [-cfg file] [-taf file]\n");
  }

  /// file list
  if (cmdOptionExists(argv, argv + argc, "-dimacs")) {
    aide.is_dimacs = true;
  }

  char* cfg_file_name = getCmdOption(argv, argv + argc, "-cfg");
  if (cfg_file_name == 0) {
    cfg_file_name = DEFAULT_CFG_FILE_NAME;
  }

  char* taf_file_name = getCmdOption(argv, argv + argc, "-taf");
  if (taf_file_name == 0) {
    taf_file_name = DEFAULT_TAF_FILE_NAME;
  }

  FILE *cfg_file = fopen(cfg_file_name, "w");

  yy::bw parser; // make a parser
  int result = parser.parse(); // and run it

  //move the file point to the begin and print the total line number
  fprintf(cfg_file, "# control flow graph and other information\n");
  fprintf(cfg_file, "shared %d\n", aide.s_vars_num);
  fprintf(cfg_file, "local %d\n",  aide.l_vars_num);

  //note the initial pc!!!!!!!!
  fprintf(cfg_file, "init %s|0,%s # initial thread state\n", 
          (aide.create_init_state(aide.s_var_init)).c_str(),
	  (aide.create_init_state(aide.l_var_init)).c_str());
  fprintf(cfg_file, "%d%s %d\n", aide.lineno, 
          " # the number of lines in BP with cand PC = ", aide.cand_count);
  cout<< aide.cand_count << ":" << aide.lineno <<endl;
  if (aide.is_dimacs)
    aide.output_control_flow_graph_dimacs(cfg_file); // output control flow graph edges
  else
    aide.output_control_flow_graph(cfg_file);
  fclose(cfg_file);

  //test_print_valid_assertion_ts(); // testing
  aide.output_assertion_ts_to_file(taf_file_name);

  return result;
}
