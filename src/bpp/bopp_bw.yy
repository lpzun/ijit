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
#include <stdio.h>
#include <stdlib.h>

#include <algorithm>
#include <iostream>
#include <assert.h>
#include <string>
#include <sstream>
#include <map>
#include <set>
#include <list>
#include <vector>
#include <stack>

  using namespace std;

  namespace std {
    /**
     * @brief convert a number to a string
     * @param _val
     * @return string
     */
    template<typename T>
      string to_string(T _val) {
      ostringstream o_str_stream;
      o_str_stream << _val;
      return o_str_stream.str();
    }
  }

  typedef unsigned short ushort;

  const static string SUCC_POSTFIX = "_";
 
  const static string KLEENE_STAR = "*";
  const static string ZERO = "0";
  const static string ONE = "1";
  const static string _AND_ = " & ";
  const static string NEGATION = "!";
  const static string RIGHT_PAREN = "(";
  const static string LEFT_PAREN = ")";

  const static string NON_CAND_MARK = "-1"; // non-candidate-pc statement
  const static string NEW_THRD_MARK = "-2"; // thread creation mark
  const static string WAIT_STMT_MARK = "-3"; // wait statement mark
  const static string BCST_STMT_MARK = "-4"; // broadcast statement mark
  const static string ATOM_STMT_MARK = "-5"; // atomic section mark

  const static string INVARIANT = "inv";

  char DEFAULT_CFG_FILE_NAME[100] = "bp.cfg";
  char DEFAULT_TAF_FILE_NAME[100] = "bp.taf";

  static set<ushort> pc_set;
  static ushort line = 0; // initialize the lineno: a stupid way to do this
  static ushort ipc = 0; // the source of cfg edge
  static ushort s_vars_num = 0; // the number of shared variables
  static ushort l_vars_num = 0; // the number of local variables

  static map<string, ushort> s_vars_list;
  static map<string, ushort> l_vars_list;
  static list<string> control_flow_graph; // control flow graph
  static map<ushort, char> s_var_init; // to record the initial shared state
  static map<ushort, char> l_var_init; // to record the initial local state
  static string goto_targets; // to output the comments
  static set<ushort> succ_stmt_label;

  static list<string> expr_symb_list;
  static list<string> assign_stmt_lhs;
  static list<list<string> > assign_stmt_rhs;
  static list<string> assign_identifiers;

  map<ushort, list<string> > valid_assertion_ts;

  ushort cand_count = 0;

  // file list
  FILE *cfg_file; // controld flow graph file
  bool is_dimacs = false;
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
  extern int yylex(yy::bw::semantic_type *yylval, yy::bw::location_type* yylloc);

  // control flow graph function list
  bool is_pc_unique(const ushort& pc);
  void create_control_flow_graph(const ushort& from, const string& wp);
  void create_control_flow_graph(const ushort& from, const ushort& to, const string& wp);
  void output_control_flow_graph(FILE *file);
  void output_control_flow_graph_dimacs(FILE *file);
  void replace_vars_with_index(string& src, const ushort& index);
  void replaceAll(std::string& str, const std::string& from, const std::string& to);

  string create_init_state(const map<ushort, char>& minit);
  bool add_to_shared_vars_list(const string& var, const ushort& index);
  bool add_to_local_vars_list(const string& var, const ushort& index);
  void add_to_expr_symb_list(const string& symbol);

  // create the weakest precondition formula of statements
  string create_goto_stmt_wp();
  string create_skip_stmt_wp();
  string create_assume_stmt_wp();
  string create_assert_stmt_wp();
  string create_assign_stmt_wp();
  void create_if_true_stmt_wp(const string& e);
  string create_if_false_stmt_wp(const string& e);
  string create_new_thr_stmt_wp(const string& pc);
  string create_wait_stmt_wp();
  string create_broadcast_stmt_wp();
  string create_atom_stmt_wp();

  string create_unassign_clause_in_wp();
  string create_invariant_clause_in_wp();
  string create_succ_vars(const string& var);

  // extract thread state from assertion
  void exhaustive_sat_solver(const list<string>& symb_list, const ushort& pc);
  vector<bool> decimal2binary(const int& n, const int& size);
  ushort power(const ushort& base, const ushort& exp);
  string create_vars_value_as_str(const vector<ushort>& sv);
  void output_assertion_ts_to_file(const string& filename);
  string convert_formula_to_cnf(const list<string>& symb_list, const bool& is_assign);
  string recov_expr_from_symb_list(const list<string>& symb_list, const bool& is_origi = false);

  // unit test
  void test_print_valid_assertion_ts();
  void test_output_parallel_assign_stmt();
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
        | labelstmt { line++; }
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
      if(add_to_shared_vars_list($1, ++s_vars_num)){
	s_var_init[s_vars_num]='*';
      }
      free($1); // free it to avoid storage leaks
    }
    | T_IDEN T_ASSIGN T_NONDET {
      if(add_to_shared_vars_list($1, ++s_vars_num)){
	s_var_init[s_vars_num] = '*';
      }
      free($1);
    }
    | T_IDEN T_ASSIGN T_INT {
      if(add_to_shared_vars_list($1, ++s_vars_num)){
	s_var_init[s_vars_num] = ($3 == 0 ? '0' : '1');
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
      if(add_to_local_vars_list($1, ++l_vars_num)){
	l_var_init[l_vars_num] = '*';
      }
      free($1);
    }
    | T_IDEN T_ASSIGN T_NONDET {
      if(add_to_local_vars_list($1, ++l_vars_num)){
	l_var_init[l_vars_num] = '*';
      }
      free($1);
    }
    | T_IDEN T_ASSIGN T_INT {
      if(add_to_local_vars_list($1, ++l_vars_num)){
	l_var_init[l_vars_num] = ($3 == 0 ? '0' : '1');
      }
      free($1);
    }
    ;

/* stmts */
initistmt: T_IDEN T_ASSIGN T_NONDET ';' {
           map<string, ushort>::iterator ifind;
	   if ((ifind = s_vars_list.find($1)) != s_vars_list.end()) {
	     s_var_init[ifind->second] = '*';
	   }
	   if ((ifind = l_vars_list.find($1)) != l_vars_list.end()) {
	     l_var_init[ifind->second] = '*';
	   }
	   free($1);
        }
        |T_IDEN T_ASSIGN T_INT ';' {
           map<string, ushort>::iterator ifind;
	   if ((ifind = s_vars_list.find($1)) != s_vars_list.end()) {
	     s_var_init[ifind->second] = ($3 == 0 ? '0' : '1');
	   }
	   if ((ifind = l_vars_list.find($1)) != l_vars_list.end()) {
	     l_var_init[ifind->second] = ($3 == 0 ? '0' : '1');
	   }
	   free($1);
        }
        ;

labelstmt: T_INT {ipc = (int)($1); if(!is_pc_unique($1)){ // pc's uniqueness
                  YYABORT; }} ':' statement {
	   cout<<"TEST:: I am in statement "<<$1<<endl;									      
	 }
         ;

statement: metastmt
	 | statement T_AND metastmt // multi-statements
         | statement T_OR metastmt
         ;

metastmt: T_GOTO {} to_line_list ';' { // "goto" statement
	  create_control_flow_graph(ipc, create_goto_stmt_wp());
	  succ_stmt_label.clear();
	  goto_targets = "";
	}
    	| T_SKIP ';' { // "skip" statement
	  create_control_flow_graph(ipc, ipc+1, create_skip_stmt_wp());	
    	}
    	| T_ASSUME '(' expr ')' ';' { // "assume" statement
	  create_control_flow_graph(ipc, ipc+1, create_assume_stmt_wp());
	  expr_symb_list.clear();
    	} 
	| T_ASSERT '(' expr ')' ';' { // "assert" statement
	  create_control_flow_graph(ipc, ipc+1, create_assert_stmt_wp());		
	  exhaustive_sat_solver(expr_symb_list, ipc);
	  expr_symb_list.clear();
	}
	| iden_list T_ASSIGN expr_list ';' { // "assignment" statement
	  create_control_flow_graph(ipc, ipc+1, create_assign_stmt_wp());	
	  // clear containers
	  assign_stmt_lhs.clear();
	  assign_stmt_rhs.clear();
	  assign_identifiers.clear();
	}
	| iden_list T_ASSIGN expr_list T_CSTR expr ';' { // "assignment constrain"  
	  string e = recov_expr_from_symb_list(expr_symb_list, true);
	  expr_symb_list.clear();

	  create_control_flow_graph(ipc, ipc+1, create_assign_stmt_wp() + _AND_ + "(" + e + ")");
	  // clear containers
	  assign_stmt_lhs.clear();
	  assign_stmt_rhs.clear();
	  assign_identifiers.clear();
	}
        | T_IF expr T_THEN metastmt T_FI ';' { // "if..then.." statement
	  string e = recov_expr_from_symb_list(expr_symb_list, true);
	  create_if_true_stmt_wp(e);
	  create_control_flow_graph(ipc, ipc+1, create_if_false_stmt_wp(e));
	  expr_symb_list.clear();
	}
        | T_START_THREAD T_GOTO T_INT ';' {
	  create_control_flow_graph(ipc, ipc + 1, create_new_thr_stmt_wp(to_string($3)));
	}
        | T_END_THREAD ';' {
	  create_control_flow_graph(ipc, ipc + 1, create_skip_stmt_wp());
        }
        | T_ATOMIC_BEGIN ';' {
  	  create_control_flow_graph(ipc, ipc + 1, create_atom_stmt_wp());
        }
        | T_ATOMIC_END ';' {
  	  create_control_flow_graph(ipc, ipc + 1, create_atom_stmt_wp());
        }
        | T_WAIT ';' {
  	  create_control_flow_graph(ipc, ipc + 1, create_wait_stmt_wp());
        }
        | T_BROADCAST ';' {
	  create_control_flow_graph(ipc, ipc + 1, create_broadcast_stmt_wp());
        }
    	;

iden_list: T_IDEN {
	  assign_identifiers.push_back($1);
	  assign_stmt_lhs.push_back($1);
	  free($1);
	}
	| iden_list ',' T_IDEN {
	  assign_identifiers.push_back($3); 
	  assign_stmt_lhs.push_back($3);
	  free($3); 
	}
	;

expr_list: expr { 
	  assign_stmt_rhs.push_back(expr_symb_list); 
	  expr_symb_list.clear();
	}
	| expr_list ',' expr { 
	  assign_stmt_rhs.push_back(expr_symb_list); 
	  expr_symb_list.clear(); 
	}
	;

to_line_list: T_INT  {
  	  succ_stmt_label.insert($1);
	  goto_targets = goto_targets + "," + to_string($1);
    	}
    	| to_line_list ',' T_INT {
	  succ_stmt_label.insert($3);
	  goto_targets = goto_targets + "," + to_string($3);
    	}
    	;

/* expressions */
expr: or_expr { }
    | expr T_TERNARY expr ':' or_expr {
      cout<<"This is a ternary expression"<<endl;
    }
    ;

or_expr: xor_expr
	| or_expr T_OR xor_expr { add_to_expr_symb_list("||");}
	;

xor_expr: and_expr
	| xor_expr '^' and_expr { add_to_expr_symb_list("^"); }
	;

and_expr: equ_expr
	| and_expr T_AND equ_expr { add_to_expr_symb_list("&&"); }
	;

equ_expr: una_expr
	| equ_expr T_EQ_OP una_expr { add_to_expr_symb_list("==");}
	| equ_expr T_NE_OP una_expr { add_to_expr_symb_list("!=");}
	;

una_op: '!' 
	;

una_expr: prm_expr
	| una_op prm_expr { add_to_expr_symb_list("!");}
	;

prm_expr: '(' expr ')' { add_to_expr_symb_list("()"); }
	| T_NONDET { add_to_expr_symb_list("*"); }
	| T_INT { add_to_expr_symb_list($1 ? "1" : "0"); }
	| T_IDEN { 
	  string id = $1;
	  if(id.at(0) == '\'') // a successor variable
	    id = SUCC_POSTFIX + id.substr(1);
	  /* else */
	  /*   id = SUCC_POSTFIX + id; */
	  add_to_expr_symb_list(id); 
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

/*
int main(int argc, char *argv[]) {
  if (cmdOptionExists(argv, argv + argc, "-h")) {
    printf("Usage: BoPP [-cfg file] [-taf file]\n");
  }

  if (cmdOptionExists(argv, argv + argc, "-dimacs")) {
    is_dimacs = true;
  }

  char* cfg_file_name = getCmdOption(argv, argv + argc, "-cfg");
  if (cfg_file_name == 0) {
    cfg_file_name = DEFAULT_CFG_FILE_NAME;
  }

  char* taf_file_name = getCmdOption(argv, argv + argc, "-taf");
  if (taf_file_name == 0) {
    taf_file_name = DEFAULT_TAF_FILE_NAME;
  }

  cfg_file = fopen(cfg_file_name, "w");

  yy::bw parser; // make a parser
  int result = parser.parse(); // and run it

  //move the file point to the begin and print the total line number
  fprintf(cfg_file, "# control flow graph and other information\n");
  fprintf(cfg_file, "shared %d\n", s_vars_num);
  fprintf(cfg_file, "local %d\n", l_vars_num);

  //note the initial pc!!!!!!!!
  fprintf(cfg_file, "init %s|0,%s # initial thread state\n", (create_init_state(s_var_init)).c_str(),
	  (create_init_state(l_var_init)).c_str());
  fprintf(cfg_file, "%d%s %d\n", line, " # the number of lines in BP with cand PC = ", cand_count);
  cout<< cand_count << ":" << line <<endl;
  if (is_dimacs)
    output_control_flow_graph_dimacs(cfg_file); // output control flow graph edges
  else
    output_control_flow_graph(cfg_file);
  fclose(cfg_file);

  //test_print_valid_assertion_ts(); // testing
  output_assertion_ts_to_file(taf_file_name);

  return result;
}*/

/**
 *
 * @param init
 * @return
 */
string create_init_state(const map<ushort, char>& minit) {
  string ss = "";
  for (map<ushort, char>::const_iterator is = minit.begin(), end = minit.end(); is != end; is++) {
    ss.push_back(',');
    ss.push_back(is->second);
  }
  if (ss.size() > 1)
    ss = ss.substr(1);
  return ss;
}

/**
 * @brief to add the shared variables to a map
 * @param var
 * @param index
 * @return
 */
bool add_to_shared_vars_list(const string& var, const ushort& index) {
  std::pair<map<string, ushort>::iterator, bool> p = s_vars_list.insert(std::pair<string, ushort>(var, index));
  return p.second;
}

/**
 * @brief to add the shared variables to a map
 * @param var
 * @param index
 * @return
 */
bool add_to_local_vars_list(const string& var, const ushort& index) {
  std::pair<map<string, ushort>::iterator, bool> p = l_vars_list.insert(std::pair<string, ushort>(var, index));
  return p.second;
}

/**
 * @brief to add the expression symbols to a list
 * @param symbol
 */
void add_to_expr_symb_list(const string& symbol) {
  expr_symb_list.push_back(symbol);
}

/*********************************** Control Flow Graph *****************************/
/**
 * @brief to determine if the pc is unique or not
 * @param pc
 */
bool is_pc_unique(const ushort& pc) {
  std::pair<set<ushort>::iterator, bool> result = pc_set.insert(pc);
  if (!result.second) {
    cerr << "syntax error: pc " << pc << " is duplicated." << endl;
    return false;
  }
  return true;
}

/**
 * @brief to create the edge for sequential statement
 * @param from
 * @param to
 * @param wp weakest precondition formula
 */
void create_control_flow_graph(const ushort& from, const ushort& to, const string& wp) {
  string edge;
  edge.append(to_string(from)).append(" -> ").append(to_string(to)).append(" ").append(wp);
  control_flow_graph.push_back(edge);
}

/**
 * @brief to create the edge for goto or non-deterministic statements
 * @param from
 * @param wp
 */
void create_control_flow_graph(const ushort& from, const string& wp) {
  for (set<ushort>::const_iterator iter = succ_stmt_label.begin(), end = succ_stmt_label.end(); iter != end; iter++) {
    string edge;
    edge.append(to_string(from)).append(" -> ").append(to_string(*iter)).append(" ").append(wp);
    control_flow_graph.push_back(edge);
  }
}

/**
 * @brief output the control flow graph to the file
 * @param file
 */
void output_control_flow_graph(FILE *file) {
  string inv = create_invariant_clause_in_wp();
  fprintf(file, "%s = %s\n", INVARIANT.c_str(), inv.c_str());
  for (list<string>::const_iterator iter = control_flow_graph.begin(), end = control_flow_graph.end(); iter != end;
       iter++) {
    fprintf(file, "%s\n", (*iter).c_str());
  }
}

/**
 * @brief output the wp in the Dimacs format
 * @param file
 */
void output_control_flow_graph_dimacs(FILE *file) {
  ushort index = s_vars_list.size() + l_vars_list.size();
  string inv = create_invariant_clause_in_wp();
  replace_vars_with_index(inv, index);
  fprintf(file, "%s = %s\n", INVARIANT.c_str(), inv.c_str());

  for (list<string>::const_iterator iter = control_flow_graph.begin(), end = control_flow_graph.end(); iter != end;
       iter++) {
    string edge = *iter;
    replace_vars_with_index(edge, index);
    fprintf(file, "%s\n", edge.c_str());
  }
}

/**
 * @brief replace variables with Dimacs index
 * @param src
 * @param index
 */
void replace_vars_with_index(string& src, const ushort& index) {
  replaceAll(src, "--", "");
  for (map<string, ushort>::const_iterator is = s_vars_list.begin(), send = s_vars_list.end(); is != send; is++) {
    replaceAll(src, create_succ_vars(is->first), to_string(is->second + l_vars_list.size() + index));
    replaceAll(src, is->first, to_string(is->second));
  }
  for (map<string, ushort>::const_iterator il = l_vars_list.begin(), lend = l_vars_list.end(); il != lend; il++) {
    replaceAll(src, create_succ_vars(il->first), to_string(il->second + index));
    replaceAll(src, il->first, to_string(il->second + s_vars_list.size()));
  }
}

/**
 *@brief replace all appearances of src in str with subst
 * @param str
 * @param src
 * @param subst
 */
void replaceAll(std::string& str, const std::string& src, const std::string& subst) {
  if (src.empty())
    return;
  size_t start_pos = 0;
  while ((start_pos = str.find(src, start_pos)) != std::string::npos) {
    str.replace(start_pos, src.length(), subst);
    start_pos += subst.length(); // in case 'to' contains 'from', like replacing 'x' with 'yx'
  }
}
/************** Create the Weakest Precondition Formula of Statements ***************/

/**
 * @brief goto statement
 * @return
 */
string create_goto_stmt_wp() {
  return NON_CAND_MARK + " " + INVARIANT;
}

/**
 * @brief skip statement
 * @return
 */
string create_skip_stmt_wp() {
  return NON_CAND_MARK + " " + INVARIANT;
}

/**
 * @brief assume statement
 * @return
 */
string create_assume_stmt_wp() {
  string expr;
  if (is_dimacs)
    expr = convert_formula_to_cnf(expr_symb_list, false);
  else
    expr = recov_expr_from_symb_list(expr_symb_list);
  string formula;
  formula.append(expr).append(_AND_);
  formula.append(INVARIANT);

  return NON_CAND_MARK + " " + formula;
}

/**
 * @brief assert statement, same as the skip statement
 * @return
 */
string create_assert_stmt_wp() {
  return NON_CAND_MARK + " " + INVARIANT;
}

/**
 * @brief assignment statement
 * 	  _x = x, where _x is the successor
 * @return string
 */
string create_assign_stmt_wp() {
  list<string>::const_iterator ii = assign_stmt_lhs.begin(), iend = assign_stmt_lhs.end();
  list<list<string> >::const_iterator ie = assign_stmt_rhs.begin(), eend = assign_stmt_rhs.end();
  string formula;
  while (ii != iend && ie != eend) {
    const string& iden = *ii;
    string expr;
    if (is_dimacs)
      expr = convert_formula_to_cnf(*ie, true);
    else
      expr = recov_expr_from_symb_list(*ie, true);

    if (expr.find_first_of('*') != std::string::npos) {
      ii++, ie++;
      continue;
    } else if (expr.compare(ZERO) == 0) {
      formula.append("-").append(create_succ_vars(iden)).append(_AND_);
    } else if (expr.compare(ONE) == 0) {
      formula.append(create_succ_vars(iden)).append(_AND_);
    } else {
      formula.append("-").append(create_succ_vars(iden)).append(" ").append(expr).append(_AND_);
      formula.append(create_succ_vars(iden)).append(" ").append("-").append(expr).append(_AND_);
    }
    ii++, ie++;
  }
  formula.append(create_unassign_clause_in_wp());

  string assign;
  for (map<string, ushort>::const_iterator is = s_vars_list.begin(); is != s_vars_list.end(); is++) {
    list<string>::iterator ifind = std::find(assign_stmt_lhs.begin(), assign_stmt_lhs.end(), is->first);
    if (ifind != assign_stmt_lhs.end()) {
      assign.append(",").append(is->first);
    }
  }

  if (assign.size() > 0){
    assign = assign.substr(1);
    cand_count++;
  }
  else
    assign = NON_CAND_MARK;

  return assign + " " + formula;
}

/**
 * @brief to create the part of wp formula, which contains the non-assignment variables
 *           call by create_assign_stmt_wp()
 * @return string the wp formula
 */
string create_unassign_clause_in_wp() {
  string formula;
  for (map<string, ushort>::const_iterator il = l_vars_list.begin(); il != l_vars_list.end(); il++) {
    list<string>::iterator ifind = std::find(assign_stmt_lhs.begin(), assign_stmt_lhs.end(), il->first);
    if (ifind == assign_stmt_lhs.end()) {
      formula.append(il->first).append(" ").append("-").append(create_succ_vars(il->first)).append(_AND_);
      formula.append("-").append(il->first).append(" ").append(create_succ_vars(il->first)).append(_AND_);
    }
  }
  formula = formula.substr(0, formula.length() - _AND_.size());
  return formula;
}

/**
 * @brief if (expr == true) then statement
 * @param e
 */
void create_if_true_stmt_wp(const string& e) {
  string edge = control_flow_graph.back();
  control_flow_graph.pop_back();
  if (e.find_first_of('*') != std::string::npos)
    control_flow_graph.push_back(edge);
  else
    control_flow_graph.push_back(edge + _AND_ + e);
}

/**
 * @brief if (expr == false); next statement
 * @param e
 * @return string
 */
string create_if_false_stmt_wp(const string& e) {
  if (e.find_first_of('*') != std::string::npos) {
    return create_invariant_clause_in_wp();
  } else if (e.at(0) == '!') {
    return create_invariant_clause_in_wp() + _AND_ + "(" + e.substr(1) + ")";
  }
  return create_invariant_clause_in_wp() + _AND_ + "(!" + e + ")";
}

/**
 * @brief start_thread goto <pc>
 * @param label
 * @return string
 */
string create_new_thr_stmt_wp(const string& pc) {
  return NEW_THRD_MARK + " " + pc;
}

/**
 * @brief wait
 * @return string
 */
string create_wait_stmt_wp() {
  return WAIT_STMT_MARK;
}

/**
 * @brief broadcast
 * @return string
 */
string create_broadcast_stmt_wp() {
  return BCST_STMT_MARK + " " + INVARIANT;
}

/**
 * @brief atomic statement: begin and end
 * @return string
 */
string create_atom_stmt_wp() {
  return ATOM_STMT_MARK + " "  + INVARIANT;
}

/**
 * @brief to create invariant wp formula:
 *          call by goto, skip, assert, and assume statements
 * @return string: the wp formula
 */
string create_invariant_clause_in_wp() {
  string formula;
  for (map<string, ushort>::const_iterator il = l_vars_list.begin(); il != l_vars_list.end(); il++) {
    formula.append(il->first).append(" ").append("-").append(create_succ_vars(il->first)).append(_AND_);
    formula.append("-").append(il->first).append(" ").append(create_succ_vars(il->first)).append(_AND_);
  }
  formula = formula.substr(0, formula.length() - _AND_.size());
  return formula;
}

/**
 * @brief to output the name of successor's variable
 * @param var
 * @return string var + SUCC_POSTFIX
 */
string create_succ_vars(const string& var) {
  return SUCC_POSTFIX + var;
}

string convert_formula_to_cnf(const list<string>& symb_list, const bool& is_assign) {
  string wp_in_cnf;

  map<string, ushort> expr_vars; // boolean variables in the formula
  ushort expr_vars_num = 0; // the number of boolean variables in the formula
  for (list<string>::const_iterator begin = symb_list.begin(), end = symb_list.end(); begin != end; begin++) {
    string symbol = *begin;
    // using regular expression here would be a better choice
    if (!(symbol.compare("&&") == 0 || symbol.compare("||") == 0 || symbol.compare("!=") == 0
	  || symbol.compare("==") == 0 || symbol.compare("^") == 0 || symbol.compare("()") == 0
	  || symbol.compare("!") == 0 || symbol.compare(ZERO) == 0 || symbol.compare(ONE) == 0
	  || symbol.compare(KLEENE_STAR) == 0)) {
      expr_vars.insert(std::pair<string, ushort>(symbol, expr_vars_num));
      expr_vars_num++;
    }
  }

  if (expr_vars_num == 0)
    return recov_expr_from_symb_list(symb_list, true);

  vector<ushort> var_indices(expr_vars.size());
  for (ushort i = 0; i < power(2, expr_vars_num); i++) {
    vector<bool> assert_vars_assignments = decimal2binary(i, expr_vars_num);

    stack<bool> comp_result_stack;
    for (list<string>::const_iterator begin = symb_list.begin(), end = symb_list.end(); begin != end; begin++) {
      string symbol = *begin;
      bool operand1, operand2;
      if (symbol.compare("&&") == 0) { // and
	operand1 = comp_result_stack.top();
	comp_result_stack.pop();
	operand2 = comp_result_stack.top();
	comp_result_stack.pop();
	comp_result_stack.push(operand2 && operand1);
      } else if (symbol.compare("||") == 0) { // or
	operand1 = comp_result_stack.top();
	comp_result_stack.pop();
	operand2 = comp_result_stack.top();
	comp_result_stack.pop();
	comp_result_stack.push(operand2 || operand1);
      } else if (symbol.compare("==") == 0) { // equal
	operand1 = comp_result_stack.top();
	comp_result_stack.pop();
	operand2 = comp_result_stack.top();
	comp_result_stack.pop();
	comp_result_stack.push(operand2 == operand1);
      } else if (symbol.compare("!=") == 0) { // not equal
	operand1 = comp_result_stack.top();
	comp_result_stack.pop();
	operand2 = comp_result_stack.top();
	comp_result_stack.pop();
	comp_result_stack.push(operand2 != operand1);
      } else if (symbol.compare("^") == 0) { // exclusive or
	operand1 = comp_result_stack.top();
	comp_result_stack.pop();
	operand2 = comp_result_stack.top();
	comp_result_stack.pop();
	comp_result_stack.push(operand2 ^ operand1);
      } else if (symbol.compare("()") == 0) { // bracket
	operand1 = comp_result_stack.top();
	comp_result_stack.pop();
	comp_result_stack.push(operand1);
      } else if (symbol.compare("!") == 0) { // negation
	operand1 = comp_result_stack.top();
	comp_result_stack.pop();
	comp_result_stack.push(!operand1);
      } else { // variables
	map<string, ushort>::iterator ifind;
	if ((ifind = expr_vars.find(symbol)) != expr_vars.end()) {
	  ushort i = ifind->second;
	  bool b_value = assert_vars_assignments[i];
	  if(is_assign){
	    if ((ifind = s_vars_list.find(symbol)) != s_vars_list.end())
	      var_indices[i] = ifind->second;
	    else if ((ifind = l_vars_list.find(symbol)) != l_vars_list.end()) 
	      var_indices[i] = ifind->second + s_vars_list.size();
	  }else{
	    if ((ifind = s_vars_list.find(symbol)) != s_vars_list.end())
	      var_indices[i] = ifind->second + s_vars_list.size() + 2 * l_vars_list.size();
	    else if ((ifind = l_vars_list.find(symbol)) != l_vars_list.end())
	      var_indices[i] = ifind->second + s_vars_list.size() + l_vars_list.size();
	  }
	  comp_result_stack.push(b_value);
	}
      }
    }

    if (!comp_result_stack.top()) {
      ushort i = 0;
      wp_in_cnf.append("& ");
      for (vector<bool>::const_iterator ib = assert_vars_assignments.begin(), end = assert_vars_assignments.end();
	   ib != end; ib++, i++) {
	//cout << *ib << " " << (*ib ? -var_indices[i] : var_indices[i]) << " ";
	wp_in_cnf.append(to_string((*ib ? -var_indices[i] : var_indices[i]))).append(" ");
      }
      //cout << endl;
    }
  }

  return wp_in_cnf.substr(2);
}

/**
 * @brief to restore the expression
 * @param symb_list
 * @param is_origi: this para is to generate the comments!!!!!!!
 * @return expression
 */
string recov_expr_from_symb_list(const list<string>& symb_list, const bool& is_origi) {
  stack<string> expr_comp;
  for (list<string>::const_iterator begin = symb_list.begin(), end = symb_list.end(); begin != end; begin++) {
    string symbol = *begin;
    string operand1 = "", operand2 = "";
    if (symbol.compare("&&") == 0) { // and
      operand1 = expr_comp.top();
      expr_comp.pop();
      operand2 = expr_comp.top();
      expr_comp.pop();
      expr_comp.push(operand2 + " && " + operand1);
    } else if (symbol.compare("||") == 0) { // or
      operand1 = expr_comp.top();
      expr_comp.pop();
      operand2 = expr_comp.top();
      expr_comp.pop();
      expr_comp.push(operand2 + " || " + operand1);
    } else if (symbol.compare("==") == 0) { // equal
      operand1 = expr_comp.top();
      expr_comp.pop();
      operand2 = expr_comp.top();
      expr_comp.pop();
      expr_comp.push(operand2 + " == " + operand1);
    } else if (symbol.compare("!=") == 0) { // not equal
      operand1 = expr_comp.top();
      expr_comp.pop();
      operand2 = expr_comp.top();
      expr_comp.pop();
      expr_comp.push(operand2 + " != " + operand1);
    } else if (symbol.compare("^") == 0) { // exclusive or
      operand1 = expr_comp.top();
      expr_comp.pop();
      operand2 = expr_comp.top();
      expr_comp.pop();
      expr_comp.push(operand2 + " ^ " + operand1);
    } else if (symbol.compare("()") == 0) { // bracket
      operand1 = expr_comp.top();
      expr_comp.pop();
      expr_comp.push("(" + operand1 + ")");
    } else if (symbol.compare(NEGATION) == 0) { // negation
      operand1 = expr_comp.top();
      expr_comp.pop();
      expr_comp.push(is_dimacs ? ("-" + operand1) : (NEGATION + operand1));
    } else if (symbol.compare(KLEENE_STAR) == 0) { // non-deterministic
      expr_comp.push(KLEENE_STAR);
    } else if (symbol.compare(ZERO) == 0) { // constant 0
      expr_comp.push(symbol);
    } else if (symbol.compare(ONE) == 0) { // constant 1
      expr_comp.push(symbol);
    } else { // variables
      expr_comp.push(is_origi ? symbol : create_succ_vars(symbol));
    }
  }
  return expr_comp.top();
}

/******************** Extract Thread States From an Assertion ***********************/

/**
 * @brief This is a customized "exhaustive" SAT solver, which can be used to extract targets
 * 	  from assertions in Boolean program. It's an exhaustive algorithm. I've no idea if
 *        we should use a more efficient SAT solver. It seems unnecessary due to that each
 *        assertion contains only very few boolean variables.
 * @note Here, we assume the assertion doesn't contain any constant, i.e., *, 0, 1.
 * @param symb_list: an expression
 * @param pc
 * @return a set of satisfiable assignments
 */
void exhaustive_sat_solver(const list<string>& symb_list, const ushort& pc) {
  list<string> s_target_list;
  map<string, ushort> assert_vars; // boolean variables in the assertion
  ushort assert_vars_num = 0; // the number of boolean variables in the assertion
  for (list<string>::const_iterator begin = symb_list.begin(), end = symb_list.end(); begin != end; begin++) {
    string symbol = *begin;
    // using regular expression here would be a better choice
    if (!(symbol.compare("&&") == 0 || symbol.compare("||") == 0 || symbol.compare("!=") == 0
	  || symbol.compare("==") == 0 || symbol.compare("^") == 0 || symbol.compare("()") == 0
	  || symbol.compare("!") == 0 || symbol.compare(ZERO) == 0 || symbol.compare(ONE) == 0)) {
      if (symbol.compare(KLEENE_STAR) == 0) {
	vector<ushort> t_shared(s_vars_list.size(), 2);
	vector<ushort> t_locals(l_vars_list.size(), 2);
	string ss;
	if (create_vars_value_as_str(t_shared).size() > 1)
	  ss.append(create_vars_value_as_str(t_shared).substr(1));
	ss.append("|").append(to_string(pc)).append(create_vars_value_as_str(t_locals));
	s_target_list.push_back(ss);
	valid_assertion_ts.insert(std::pair<ushort, list<string> >(pc, s_target_list));
	return;
      } else {
	assert_vars.insert(std::pair<string, ushort>(symbol, assert_vars_num));
	assert_vars_num++;
      }
    }
  }

  for (ushort i = 0; i < power(2, assert_vars_num); i++) {
    vector<bool> assert_vars_assignments = decimal2binary(i, assert_vars_num);
    vector<ushort> t_shared(s_vars_list.size(), 2);
    vector<ushort> t_locals(l_vars_list.size(), 2);

    stack<bool> comp_result_stack;
    for (list<string>::const_iterator begin = symb_list.begin(), end = symb_list.end(); begin != end; begin++) {
      string symbol = *begin;
      bool operand1, operand2;
      if (symbol.compare("&&") == 0) { // and
	operand1 = comp_result_stack.top();
	comp_result_stack.pop();
	operand2 = comp_result_stack.top();
	comp_result_stack.pop();
	comp_result_stack.push(operand2 && operand1);
      } else if (symbol.compare("||") == 0) { // or
	operand1 = comp_result_stack.top();
	comp_result_stack.pop();
	operand2 = comp_result_stack.top();
	comp_result_stack.pop();
	comp_result_stack.push(operand2 || operand1);
      } else if (symbol.compare("==") == 0) { // equal
	operand1 = comp_result_stack.top();
	comp_result_stack.pop();
	operand2 = comp_result_stack.top();
	comp_result_stack.pop();
	comp_result_stack.push(operand2 == operand1);
      } else if (symbol.compare("!=") == 0) { // not equal
	operand1 = comp_result_stack.top();
	comp_result_stack.pop();
	operand2 = comp_result_stack.top();
	comp_result_stack.pop();
	comp_result_stack.push(operand2 != operand1);
      } else if (symbol.compare("^") == 0) { // exclusive or
	operand1 = comp_result_stack.top();
	comp_result_stack.pop();
	operand2 = comp_result_stack.top();
	comp_result_stack.pop();
	comp_result_stack.push(operand2 ^ operand1);
      } else if (symbol.compare("()") == 0) { // bracket
	operand1 = comp_result_stack.top();
	comp_result_stack.pop();
	comp_result_stack.push((operand1));
      } else if (symbol.compare("!") == 0) { // negation
	operand1 = comp_result_stack.top();
	comp_result_stack.pop();
	comp_result_stack.push(!operand1);
      } else if (symbol.compare(ZERO) == 0) { // constant 0
	comp_result_stack.push(false);
      } else if (symbol.compare(ONE) == 0) { // constant 1
	comp_result_stack.push(true);
      } else { // variables
	map<string, ushort>::iterator ifind;
	if ((ifind = assert_vars.find(symbol)) != assert_vars.end()) {
	  bool b_value = assert_vars_assignments[ifind->second];
	  comp_result_stack.push(b_value);
	  if ((ifind = s_vars_list.find(symbol)) != s_vars_list.end())
	    t_shared[ifind->second - 1] = b_value;
	  else if ((ifind = l_vars_list.find(symbol)) != l_vars_list.end())
	    t_locals[ifind->second - 1] = b_value;
	}
      }
    }

    if (!comp_result_stack.top()) {
      string ss;
      if (create_vars_value_as_str(t_shared).size() > 1)
	ss.append(create_vars_value_as_str(t_shared).substr(1));
      ss.append("|").append(to_string(pc)).append(create_vars_value_as_str(t_locals));
      s_target_list.push_back(ss);
    }
  }
  valid_assertion_ts.insert(std::pair<ushort, list<string> >(pc, s_target_list));
}


/**
 * @brief covert a decimal to binary
 * @param n
 * @param size
 * @return vector<bool>: the first element is the least-significant bit
 */
vector<bool> decimal2binary(const int& n, const int& size) {
  vector<bool> bv(size, false);
  ushort dividend = n, i = 0;
  do {
    bool mod = dividend % 2;
    dividend = dividend / 2;
    bv[i++] = mod;
  } while (dividend >= 1);
  return bv;
}

/**
 * @brief power computation
 * @param base
 * @param exp
 * @return
 */
ushort power(const ushort& base, const ushort& exp) {
  ushort result = 1;
  for (ushort i = 0; i < exp; ++i)
    result *= base;
  return result;
}

/**
 * @brief convert the vector<ushort> to a shared/local state
 * @param sv
 */
string create_vars_value_as_str(const vector<ushort>& sv) {
  string target;
  for (vector<ushort>::const_iterator iter = sv.begin(), end = sv.end(); iter != end; iter++) {
    const ushort val = *iter;
    switch (val) {
    case 0:
      target.append(",0");
      break;
    case 1:
      target.append(",1");
      break;
    case 2:
      target.append(",*");
      break;
    }
  }
  return target;
}

/**
 * @brief to print thread state extracted from assertion
 */
void output_assertion_ts_to_file(const string& filename) {
  FILE* file = fopen(filename.c_str(), "w");
  for (map<ushort, list<string> >::const_iterator iter = valid_assertion_ts.begin(), end = valid_assertion_ts.end();
       iter != end; iter++) {
    const ushort& pc = iter->first;
    const list<string>& tss = iter->second;
    fprintf(file, "#%d\n", pc);
    for (list<string>::const_iterator l_iter = tss.begin(), l_end = tss.end(); l_iter != l_end; l_iter++) {
      const string& assign = *l_iter;
      fprintf(file, "%s\n", assign.c_str());
    }
    fprintf(file, "\n");
  }
  fclose(file);
}

/********************************** Some Testing Methods ****************************/
void test_output_parallel_assign_stmt() {
  list<string>::const_iterator i_iter = assign_stmt_lhs.begin(), i_end = assign_stmt_lhs.end();
  list<list<string> >::const_iterator e_iter = assign_stmt_rhs.begin(), e_end = assign_stmt_rhs.end();
  while (i_iter != i_end && e_iter != e_end) {
    const string& iden = *i_iter;
    const list<string>& expr = *e_iter;
    cout << iden << ":=" << recov_expr_from_symb_list(expr, true) << endl;
    i_iter++, e_iter++;
  }
}

/**
 * @brief to print thread state extracted from assertion
 */
void test_print_valid_assertion_ts() {
  for (map<ushort, list<string> >::const_iterator iter = valid_assertion_ts.begin(), end = valid_assertion_ts.end();
       iter != end; iter++) {
    const ushort& pc = iter->first;
    const list<string>& tss = iter->second;
    for (list<string>::const_iterator l_iter = tss.begin(), l_end = tss.end(); l_iter != l_end; l_iter++) {
      const string& assign = *l_iter;
      cout << pc << ":" << assign << endl;
    }
  }
}
