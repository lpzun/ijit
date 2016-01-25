// A Bison parser, made by GNU Bison 3.0.2.

// Skeleton implementation for Bison LALR(1) parsers in C++

// Copyright (C) 2002-2013 Free Software Foundation, Inc.

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

// As a special exception, you may create a larger work that contains
// part or all of the Bison parser skeleton and distribute that work
// under terms of your choice, so long as that work isn't itself a
// parser generator using the skeleton or a modified version thereof
// as a parser skeleton.  Alternatively, if you modify or redistribute
// the parser skeleton itself, you may (at your option) remove this
// special exception, which will cause the skeleton and the resulting
// Bison output files to be licensed under the GNU General Public
// License without this special exception.

// This special exception was added by the Free Software Foundation in
// version 2.2 of Bison.


// First part of user declarations.
#line 30 "bopp.y" // lalr1.cc:399


#line 39 "bopp.tab.cc" // lalr1.cc:399

# ifndef YY_NULLPTR
#  if defined __cplusplus && 201103L <= __cplusplus
#   define YY_NULLPTR nullptr
#  else
#   define YY_NULLPTR 0
#  endif
# endif

#include "bopp.tab.hh"

// User implementation prologue.
#line 77 "bopp.y" // lalr1.cc:407

  extern int yylex(yy::bp::semantic_type *yylval, yy::bp::location_type* yylloc);

#line 56 "bopp.tab.cc" // lalr1.cc:407


#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> // FIXME: INFRINGES ON USER NAME SPACE.
#   define YY_(msgid) dgettext ("bison-runtime", msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(msgid) msgid
# endif
#endif

#define YYRHSLOC(Rhs, K) ((Rhs)[K].location)
/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

# ifndef YYLLOC_DEFAULT
#  define YYLLOC_DEFAULT(Current, Rhs, N)                               \
    do                                                                  \
      if (N)                                                            \
        {                                                               \
          (Current).begin  = YYRHSLOC (Rhs, 1).begin;                   \
          (Current).end    = YYRHSLOC (Rhs, N).end;                     \
        }                                                               \
      else                                                              \
        {                                                               \
          (Current).begin = (Current).end = YYRHSLOC (Rhs, 0).end;      \
        }                                                               \
    while (/*CONSTCOND*/ false)
# endif


// Suppress unused-variable warnings by "using" E.
#define YYUSE(E) ((void) (E))

// Enable debugging if requested.
#if YYDEBUG

// A pseudo ostream that takes yydebug_ into account.
# define YYCDEBUG if (yydebug_) (*yycdebug_)

# define YY_SYMBOL_PRINT(Title, Symbol)         \
  do {                                          \
    if (yydebug_)                               \
    {                                           \
      *yycdebug_ << Title << ' ';               \
      yy_print_ (*yycdebug_, Symbol);           \
      *yycdebug_ << std::endl;                  \
    }                                           \
  } while (false)

# define YY_REDUCE_PRINT(Rule)          \
  do {                                  \
    if (yydebug_)                       \
      yy_reduce_print_ (Rule);          \
  } while (false)

# define YY_STACK_PRINT()               \
  do {                                  \
    if (yydebug_)                       \
      yystack_print_ ();                \
  } while (false)

#else // !YYDEBUG

# define YYCDEBUG if (false) std::cerr
# define YY_SYMBOL_PRINT(Title, Symbol)  YYUSE(Symbol)
# define YY_REDUCE_PRINT(Rule)           static_cast<void>(0)
# define YY_STACK_PRINT()                static_cast<void>(0)

#endif // !YYDEBUG

#define yyerrok         (yyerrstatus_ = 0)
#define yyclearin       (yyempty = true)

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab
#define YYRECOVERING()  (!!yyerrstatus_)


namespace yy {
#line 142 "bopp.tab.cc" // lalr1.cc:474

  /* Return YYSTR after stripping away unnecessary quotes and
     backslashes, so that it's suitable for yyerror.  The heuristic is
     that double-quoting is unnecessary unless the string contains an
     apostrophe, a comma, or backslash (other than backslash-backslash).
     YYSTR is taken from yytname.  */
  std::string
  bp::yytnamerr_ (const char *yystr)
  {
    if (*yystr == '"')
      {
        std::string yyr = "";
        char const *yyp = yystr;

        for (;;)
          switch (*++yyp)
            {
            case '\'':
            case ',':
              goto do_not_strip_quotes;

            case '\\':
              if (*++yyp != '\\')
                goto do_not_strip_quotes;
              // Fall through.
            default:
              yyr += *yyp;
              break;

            case '"':
              return yyr;
            }
      do_not_strip_quotes: ;
      }

    return yystr;
  }


  /// Build a parser object.
  bp::bp (fw_aide &aide_yyarg)
    :
#if YYDEBUG
      yydebug_ (false),
      yycdebug_ (&std::cerr),
#endif
      aide (aide_yyarg)
  {}

  bp::~bp ()
  {}


  /*---------------.
  | Symbol types.  |
  `---------------*/

  inline
  bp::syntax_error::syntax_error (const location_type& l, const std::string& m)
    : std::runtime_error (m)
    , location (l)
  {}

  // basic_symbol.
  template <typename Base>
  inline
  bp::basic_symbol<Base>::basic_symbol ()
    : value ()
  {}

  template <typename Base>
  inline
  bp::basic_symbol<Base>::basic_symbol (const basic_symbol& other)
    : Base (other)
    , value ()
    , location (other.location)
  {
    value = other.value;
  }


  template <typename Base>
  inline
  bp::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, const semantic_type& v, const location_type& l)
    : Base (t)
    , value (v)
    , location (l)
  {}


  /// Constructor for valueless symbols.
  template <typename Base>
  inline
  bp::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, const location_type& l)
    : Base (t)
    , value ()
    , location (l)
  {}

  template <typename Base>
  inline
  bp::basic_symbol<Base>::~basic_symbol ()
  {
  }

  template <typename Base>
  inline
  void
  bp::basic_symbol<Base>::move (basic_symbol& s)
  {
    super_type::move(s);
    value = s.value;
    location = s.location;
  }

  // by_type.
  inline
  bp::by_type::by_type ()
     : type (empty)
  {}

  inline
  bp::by_type::by_type (const by_type& other)
    : type (other.type)
  {}

  inline
  bp::by_type::by_type (token_type t)
    : type (yytranslate_ (t))
  {}

  inline
  void
  bp::by_type::move (by_type& that)
  {
    type = that.type;
    that.type = empty;
  }

  inline
  int
  bp::by_type::type_get () const
  {
    return type;
  }


  // by_state.
  inline
  bp::by_state::by_state ()
    : state (empty)
  {}

  inline
  bp::by_state::by_state (const by_state& other)
    : state (other.state)
  {}

  inline
  void
  bp::by_state::move (by_state& that)
  {
    state = that.state;
    that.state = empty;
  }

  inline
  bp::by_state::by_state (state_type s)
    : state (s)
  {}

  inline
  bp::symbol_number_type
  bp::by_state::type_get () const
  {
    return state == empty ? 0 : yystos_[state];
  }

  inline
  bp::stack_symbol_type::stack_symbol_type ()
  {}


  inline
  bp::stack_symbol_type::stack_symbol_type (state_type s, symbol_type& that)
    : super_type (s, that.location)
  {
    value = that.value;
    // that is emptied.
    that.type = empty;
  }

  inline
  bp::stack_symbol_type&
  bp::stack_symbol_type::operator= (const stack_symbol_type& that)
  {
    state = that.state;
    value = that.value;
    location = that.location;
    return *this;
  }


  template <typename Base>
  inline
  void
  bp::yy_destroy_ (const char* yymsg, basic_symbol<Base>& yysym) const
  {
    if (yymsg)
      YY_SYMBOL_PRINT (yymsg, yysym);

    // User destructor.
    YYUSE (yysym.type_get ());
  }

#if YYDEBUG
  template <typename Base>
  void
  bp::yy_print_ (std::ostream& yyo,
                                     const basic_symbol<Base>& yysym) const
  {
    std::ostream& yyoutput = yyo;
    YYUSE (yyoutput);
    symbol_number_type yytype = yysym.type_get ();
    yyo << (yytype < yyntokens_ ? "token" : "nterm")
        << ' ' << yytname_[yytype] << " ("
        << yysym.location << ": ";
    YYUSE (yytype);
    yyo << ')';
  }
#endif

  inline
  void
  bp::yypush_ (const char* m, state_type s, symbol_type& sym)
  {
    stack_symbol_type t (s, sym);
    yypush_ (m, t);
  }

  inline
  void
  bp::yypush_ (const char* m, stack_symbol_type& s)
  {
    if (m)
      YY_SYMBOL_PRINT (m, s);
    yystack_.push (s);
  }

  inline
  void
  bp::yypop_ (unsigned int n)
  {
    yystack_.pop (n);
  }

#if YYDEBUG
  std::ostream&
  bp::debug_stream () const
  {
    return *yycdebug_;
  }

  void
  bp::set_debug_stream (std::ostream& o)
  {
    yycdebug_ = &o;
  }


  bp::debug_level_type
  bp::debug_level () const
  {
    return yydebug_;
  }

  void
  bp::set_debug_level (debug_level_type l)
  {
    yydebug_ = l;
  }
#endif // YYDEBUG

  inline bp::state_type
  bp::yy_lr_goto_state_ (state_type yystate, int yysym)
  {
    int yyr = yypgoto_[yysym - yyntokens_] + yystate;
    if (0 <= yyr && yyr <= yylast_ && yycheck_[yyr] == yystate)
      return yytable_[yyr];
    else
      return yydefgoto_[yysym - yyntokens_];
  }

  inline bool
  bp::yy_pact_value_is_default_ (int yyvalue)
  {
    return yyvalue == yypact_ninf_;
  }

  inline bool
  bp::yy_table_value_is_error_ (int yyvalue)
  {
    return yyvalue == yytable_ninf_;
  }

  int
  bp::parse ()
  {
    /// Whether yyla contains a lookahead.
    bool yyempty = true;

    // State.
    int yyn;
    /// Length of the RHS of the rule being reduced.
    int yylen = 0;

    // Error handling.
    int yynerrs_ = 0;
    int yyerrstatus_ = 0;

    /// The lookahead symbol.
    symbol_type yyla;

    /// The locations where the error started and ended.
    stack_symbol_type yyerror_range[3];

    /// The return value of parse ().
    int yyresult;

    // FIXME: This shoud be completely indented.  It is not yet to
    // avoid gratuitous conflicts when merging into the master branch.
    try
      {
    YYCDEBUG << "Starting parse" << std::endl;


    // User initialization code.
    #line 81 "bopp.y" // lalr1.cc:729
{
  // add filename to location info here
  yyla.location.begin.filename = yyla.location.end.filename = new std::string("stdin");
 }

#line 486 "bopp.tab.cc" // lalr1.cc:729

    /* Initialize the stack.  The initial state will be set in
       yynewstate, since the latter expects the semantical and the
       location values to have been already stored, initialize these
       stacks with a primary value.  */
    yystack_.clear ();
    yypush_ (YY_NULLPTR, 0, yyla);

    // A new symbol was pushed on the stack.
  yynewstate:
    YYCDEBUG << "Entering state " << yystack_[0].state << std::endl;

    // Accept?
    if (yystack_[0].state == yyfinal_)
      goto yyacceptlab;

    goto yybackup;

    // Backup.
  yybackup:

    // Try to take a decision without lookahead.
    yyn = yypact_[yystack_[0].state];
    if (yy_pact_value_is_default_ (yyn))
      goto yydefault;

    // Read a lookahead token.
    if (yyempty)
      {
        YYCDEBUG << "Reading a token: ";
        try
          {
            yyla.type = yytranslate_ (yylex (&yyla.value, &yyla.location));
          }
        catch (const syntax_error& yyexc)
          {
            error (yyexc);
            goto yyerrlab1;
          }
        yyempty = false;
      }
    YY_SYMBOL_PRINT ("Next token is", yyla);

    /* If the proper action on seeing token YYLA.TYPE is to reduce or
       to detect an error, take that action.  */
    yyn += yyla.type_get ();
    if (yyn < 0 || yylast_ < yyn || yycheck_[yyn] != yyla.type_get ())
      goto yydefault;

    // Reduce or error.
    yyn = yytable_[yyn];
    if (yyn <= 0)
      {
        if (yy_table_value_is_error_ (yyn))
          goto yyerrlab;
        yyn = -yyn;
        goto yyreduce;
      }

    // Discard the token being shifted.
    yyempty = true;

    // Count tokens shifted since error; after three, turn off error status.
    if (yyerrstatus_)
      --yyerrstatus_;

    // Shift the lookahead token.
    yypush_ ("Shifting", yyn, yyla);
    goto yynewstate;

  /*-----------------------------------------------------------.
  | yydefault -- do the default action for the current state.  |
  `-----------------------------------------------------------*/
  yydefault:
    yyn = yydefact_[yystack_[0].state];
    if (yyn == 0)
      goto yyerrlab;
    goto yyreduce;

  /*-----------------------------.
  | yyreduce -- Do a reduction.  |
  `-----------------------------*/
  yyreduce:
    yylen = yyr2_[yyn];
    {
      stack_symbol_type yylhs;
      yylhs.state = yy_lr_goto_state_(yystack_[yylen].state, yyr1_[yyn]);
      /* If YYLEN is nonzero, implement the default value of the
         action: '$$ = $1'.  Otherwise, use the top of the stack.

         Otherwise, the following line sets YYLHS.VALUE to garbage.
         This behavior is undocumented and Bison users should not rely
         upon it.  */
      if (yylen)
        yylhs.value = yystack_[yylen - 1].value;
      else
        yylhs.value = yystack_[0].value;

      // Compute the default @$.
      {
        slice<stack_symbol_type, stack_type> slice (yystack_, yylen);
        YYLLOC_DEFAULT (yylhs.location, slice, yylen);
      }

      // Perform the reduction.
      YY_REDUCE_PRINT (yyn);
      try
        {
          switch (yyn)
            {
  case 19:
#line 138 "bopp.y" // lalr1.cc:847
    {
  aide.add_vars((yystack_[0].value.t_str), sool::N, true);
  /* aide.s_vars_list.emplace($1, ++aide.s_vars_num); */
  /* aide.s_vars_init[aide.s_vars_num] = '*'; */
  free((yystack_[0].value.t_str)); // free it to avoid storage leaks
 }
#line 605 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 20:
#line 144 "bopp.y" // lalr1.cc:847
    {
  aide.add_vars((yystack_[2].value.t_str), sool::N, true);
  /* aide.s_vars_list.emplace($1, ++aide.s_vars_num); */
  /* aide.s_vars_init[aide.s_vars_num] = '*'; */
  free((yystack_[2].value.t_str)); // free it to avoid storage leaks
 }
#line 616 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 21:
#line 150 "bopp.y" // lalr1.cc:847
    {
  aide.add_vars((yystack_[2].value.t_str), (yystack_[0].value.t_val) == 0 ? sool::F : sool::N, true);
  /* aide.s_vars_list.emplace($1, ++aide.s_vars_num); */
  /* aide.s_vars_init[aide.s_vars_num] = (); */
  free((yystack_[2].value.t_str)); // free it to avoid storage leaks
 }
#line 627 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 22:
#line 159 "bopp.y" // lalr1.cc:847
    { }
#line 633 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 24:
#line 163 "bopp.y" // lalr1.cc:847
    {}
#line 639 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 25:
#line 166 "bopp.y" // lalr1.cc:847
    {
  aide.add_vars((yystack_[0].value.t_str), sool::N, false);
  /* aide.l_vars_list.emplace($1, ++aide.l_vars_num); */
  /* aide.l_vars_init[aide.l_vars_num] = '*'; */
  free((yystack_[0].value.t_str));
 }
#line 650 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 26:
#line 172 "bopp.y" // lalr1.cc:847
    {
  aide.add_vars((yystack_[2].value.t_str), sool::N, false);
  /* aide.l_vars_list.emplace($1, ++aide.l_vars_num); */
  /* aide.l_vars_init[aide.l_vars_num] = '*'; */
  free((yystack_[2].value.t_str));
 }
#line 661 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 27:
#line 178 "bopp.y" // lalr1.cc:847
    {
  aide.add_vars((yystack_[2].value.t_str), (yystack_[0].value.t_val) == 0 ? sool::F : sool::N, false);
  /* aide.l_vars_list.emplace($1, ++aide.l_vars_num); */
  /* aide.l_vars_init[aide.l_vars_num] = ($3 == 0 ? '0' : '1'); */
  free((yystack_[2].value.t_str));
 }
#line 672 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 28:
#line 188 "bopp.y" // lalr1.cc:847
    {
  aide.init_vars((yystack_[3].value.t_str), sool::N);
  free((yystack_[3].value.t_str));
 }
#line 681 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 29:
#line 192 "bopp.y" // lalr1.cc:847
    {
  aide.init_vars((yystack_[3].value.t_str), (yystack_[1].value.t_val) == 0 ? sool::F : sool::N);
  free((yystack_[3].value.t_str));
 }
#line 690 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 30:
#line 198 "bopp.y" // lalr1.cc:847
    { 
  ++aide.lineno; // counting the program counters
  aide.ipc = (int)((yystack_[0].value.t_val)); // obtain current pc
  if(!aide.is_pc_unique((yystack_[0].value.t_val))) // pc's uniqueness
    YYABORT; 
 }
#line 701 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 31:
#line 203 "bopp.y" // lalr1.cc:847
    {
   //cout << "TEST:: I am in statement " << $1 <<endl;
   }
#line 709 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 35:
#line 213 "bopp.y" // lalr1.cc:847
    { // "skip" statement
  aide.add_edge(aide.ipc, aide.ipc+1, type_stmt::SKIP);	
  }
#line 717 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 36:
#line 216 "bopp.y" // lalr1.cc:847
    {}
#line 723 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 37:
#line 216 "bopp.y" // lalr1.cc:847
    { // "goto" statement
  aide.add_edge(aide.ipc, type_stmt::GOTO);
  aide.succ_pc_set.clear();
  }
#line 732 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 38:
#line 220 "bopp.y" // lalr1.cc:847
    {// "parallel assignment" statement
  aide.add_edge(aide.ipc, aide.ipc+1, type_stmt::ASSG);	
  // reset containers
  aide.assign_stmt_lhs.clear();
  aide.assign_stmt_rhs.clear();
 }
#line 743 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 39:
#line 226 "bopp.y" // lalr1.cc:847
    {// "PA with constrain" 
  aide.add_edge(aide.ipc, aide.ipc+1, type_stmt::ASSG, true);
  // reset containers
  aide.expr_in_list.clear();
  aide.assign_stmt_lhs.clear();
  aide.assign_stmt_rhs.clear();
 }
#line 755 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 40:
#line 233 "bopp.y" // lalr1.cc:847
    { // "if...then goto..." statement
  aide.add_edge(aide.ipc, (yystack_[3].value.t_val), type_stmt::IFEL, true);
  aide.expr_in_list.clear();
 }
#line 764 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 41:
#line 237 "bopp.y" // lalr1.cc:847
    { // "assert" statement
  aide.add_edge(aide.ipc, aide.ipc+1, type_stmt::ASSE);		
  //aide.all_sat_solver(aide.expr_in_list, aide.ipc);
  aide.expr_in_list.clear();
  }
#line 774 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 42:
#line 242 "bopp.y" // lalr1.cc:847
    { // "assume" statement
  aide.add_edge(aide.ipc, aide.ipc+1, type_stmt::ASSU, true);
  aide.expr_in_list.clear();
  }
#line 783 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 43:
#line 246 "bopp.y" // lalr1.cc:847
    { // "thread creation" statement
  aide.add_edge(aide.ipc, (yystack_[1].value.t_val), type_stmt::NTHR);
 }
#line 791 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 44:
#line 249 "bopp.y" // lalr1.cc:847
    { // thread termination statement
  aide.add_edge(aide.ipc, aide.ipc+1, type_stmt::ETHR);
  }
#line 799 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 45:
#line 252 "bopp.y" // lalr1.cc:847
    { // atomic section beginning
  aide.add_edge(aide.ipc, aide.ipc+1, type_stmt::ATOM);
  }
#line 807 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 46:
#line 255 "bopp.y" // lalr1.cc:847
    { // atomic section ending
  aide.add_edge(aide.ipc, aide.ipc+1, type_stmt::EATM);
  }
#line 815 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 47:
#line 258 "bopp.y" // lalr1.cc:847
    { // broadcast statement
  aide.add_edge(aide.ipc, aide.ipc+1, type_stmt::BCST);
  }
#line 823 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 48:
#line 261 "bopp.y" // lalr1.cc:847
    { // wait statement
  aide.add_edge(aide.ipc, aide.ipc+1, type_stmt::WAIT);
  }
#line 831 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 49:
#line 266 "bopp.y" // lalr1.cc:847
    {
  aide.assign_stmt_lhs.emplace_back((yystack_[0].value.t_str));
  free((yystack_[0].value.t_str));
 }
#line 840 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 50:
#line 270 "bopp.y" // lalr1.cc:847
    {
  aide.assign_stmt_lhs.emplace_back((yystack_[0].value.t_str));
  free((yystack_[0].value.t_str)); 
  }
#line 849 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 51:
#line 276 "bopp.y" // lalr1.cc:847
    { 
  aide.assign_stmt_rhs.emplace_back(aide.expr_in_list); 
  aide.expr_in_list.clear();
 }
#line 858 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 52:
#line 280 "bopp.y" // lalr1.cc:847
    { 
  aide.assign_stmt_rhs.emplace_back(aide.expr_in_list); 
  aide.expr_in_list.clear(); 
  }
#line 867 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 53:
#line 286 "bopp.y" // lalr1.cc:847
    {
  aide.succ_pc_set.emplace((yystack_[0].value.t_val));
 }
#line 875 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 54:
#line 289 "bopp.y" // lalr1.cc:847
    {
  aide.succ_pc_set.emplace((yystack_[0].value.t_val));
  }
#line 883 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 55:
#line 295 "bopp.y" // lalr1.cc:847
    { }
#line 889 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 56:
#line 296 "bopp.y" // lalr1.cc:847
    {
  cout<<"This is a ternary expression"<<endl;
 }
#line 897 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 58:
#line 302 "bopp.y" // lalr1.cc:847
    { aide.add_to_expr_in_list("|"); }
#line 903 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 60:
#line 306 "bopp.y" // lalr1.cc:847
    { aide.add_to_expr_in_list("^"); }
#line 909 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 62:
#line 310 "bopp.y" // lalr1.cc:847
    { aide.add_to_expr_in_list("&"); }
#line 915 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 64:
#line 314 "bopp.y" // lalr1.cc:847
    { aide.add_to_expr_in_list( "="); }
#line 921 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 65:
#line 315 "bopp.y" // lalr1.cc:847
    { aide.add_to_expr_in_list("!="); }
#line 927 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 68:
#line 322 "bopp.y" // lalr1.cc:847
    { aide.add_to_expr_in_list("!"); }
#line 933 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 69:
#line 325 "bopp.y" // lalr1.cc:847
    { aide.add_to_expr_in_list("()"); }
#line 939 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 70:
#line 326 "bopp.y" // lalr1.cc:847
    { aide.add_to_expr_in_list("*"); }
#line 945 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 71:
#line 327 "bopp.y" // lalr1.cc:847
    { aide.add_to_expr_in_list((yystack_[0].value.t_val) ? "1" : "0"); }
#line 951 "bopp.tab.cc" // lalr1.cc:847
    break;

  case 72:
#line 328 "bopp.y" // lalr1.cc:847
    { 
  string id = (yystack_[0].value.t_str);
  if(id.at(0) == '\'') // a successor variable
    id = aide.SUCC_POSTFIX + id.substr(1);
    aide.add_to_expr_in_list(id); 
    free((yystack_[0].value.t_str));
  }
#line 963 "bopp.tab.cc" // lalr1.cc:847
    break;


#line 967 "bopp.tab.cc" // lalr1.cc:847
            default:
              break;
            }
        }
      catch (const syntax_error& yyexc)
        {
          error (yyexc);
          YYERROR;
        }
      YY_SYMBOL_PRINT ("-> $$ =", yylhs);
      yypop_ (yylen);
      yylen = 0;
      YY_STACK_PRINT ();

      // Shift the result of the reduction.
      yypush_ (YY_NULLPTR, yylhs);
    }
    goto yynewstate;

  /*--------------------------------------.
  | yyerrlab -- here on detecting error.  |
  `--------------------------------------*/
  yyerrlab:
    // If not already recovering from an error, report this error.
    if (!yyerrstatus_)
      {
        ++yynerrs_;
        error (yyla.location, yysyntax_error_ (yystack_[0].state,
                                           yyempty ? yyempty_ : yyla.type_get ()));
      }


    yyerror_range[1].location = yyla.location;
    if (yyerrstatus_ == 3)
      {
        /* If just tried and failed to reuse lookahead token after an
           error, discard it.  */

        // Return failure if at end of input.
        if (yyla.type_get () == yyeof_)
          YYABORT;
        else if (!yyempty)
          {
            yy_destroy_ ("Error: discarding", yyla);
            yyempty = true;
          }
      }

    // Else will try to reuse lookahead token after shifting the error token.
    goto yyerrlab1;


  /*---------------------------------------------------.
  | yyerrorlab -- error raised explicitly by YYERROR.  |
  `---------------------------------------------------*/
  yyerrorlab:

    /* Pacify compilers like GCC when the user code never invokes
       YYERROR and the label yyerrorlab therefore never appears in user
       code.  */
    if (false)
      goto yyerrorlab;
    yyerror_range[1].location = yystack_[yylen - 1].location;
    /* Do not reclaim the symbols of the rule whose action triggered
       this YYERROR.  */
    yypop_ (yylen);
    yylen = 0;
    goto yyerrlab1;

  /*-------------------------------------------------------------.
  | yyerrlab1 -- common code for both syntax error and YYERROR.  |
  `-------------------------------------------------------------*/
  yyerrlab1:
    yyerrstatus_ = 3;   // Each real token shifted decrements this.
    {
      stack_symbol_type error_token;
      for (;;)
        {
          yyn = yypact_[yystack_[0].state];
          if (!yy_pact_value_is_default_ (yyn))
            {
              yyn += yyterror_;
              if (0 <= yyn && yyn <= yylast_ && yycheck_[yyn] == yyterror_)
                {
                  yyn = yytable_[yyn];
                  if (0 < yyn)
                    break;
                }
            }

          // Pop the current state because it cannot handle the error token.
          if (yystack_.size () == 1)
            YYABORT;

          yyerror_range[1].location = yystack_[0].location;
          yy_destroy_ ("Error: popping", yystack_[0]);
          yypop_ ();
          YY_STACK_PRINT ();
        }

      yyerror_range[2].location = yyla.location;
      YYLLOC_DEFAULT (error_token.location, yyerror_range, 2);

      // Shift the error token.
      error_token.state = yyn;
      yypush_ ("Shifting", error_token);
    }
    goto yynewstate;

    // Accept.
  yyacceptlab:
    yyresult = 0;
    goto yyreturn;

    // Abort.
  yyabortlab:
    yyresult = 1;
    goto yyreturn;

  yyreturn:
    if (!yyempty)
      yy_destroy_ ("Cleanup: discarding lookahead", yyla);

    /* Do not reclaim the symbols of the rule whose action triggered
       this YYABORT or YYACCEPT.  */
    yypop_ (yylen);
    while (1 < yystack_.size ())
      {
        yy_destroy_ ("Cleanup: popping", yystack_[0]);
        yypop_ ();
      }

    return yyresult;
  }
    catch (...)
      {
        YYCDEBUG << "Exception caught: cleaning lookahead and stack"
                 << std::endl;
        // Do not try to display the values of the reclaimed symbols,
        // as their printer might throw an exception.
        if (!yyempty)
          yy_destroy_ (YY_NULLPTR, yyla);

        while (1 < yystack_.size ())
          {
            yy_destroy_ (YY_NULLPTR, yystack_[0]);
            yypop_ ();
          }
        throw;
      }
  }

  void
  bp::error (const syntax_error& yyexc)
  {
    error (yyexc.location, yyexc.what());
  }

  // Generate an error message.
  std::string
  bp::yysyntax_error_ (state_type yystate, symbol_number_type yytoken) const
  {
    std::string yyres;
    // Number of reported tokens (one for the "unexpected", one per
    // "expected").
    size_t yycount = 0;
    // Its maximum.
    enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
    // Arguments of yyformat.
    char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];

    /* There are many possibilities here to consider:
       - If this state is a consistent state with a default action, then
         the only way this function was invoked is if the default action
         is an error action.  In that case, don't check for expected
         tokens because there are none.
       - The only way there can be no lookahead present (in yytoken) is
         if this state is a consistent state with a default action.
         Thus, detecting the absence of a lookahead is sufficient to
         determine that there is no unexpected or expected token to
         report.  In that case, just report a simple "syntax error".
       - Don't assume there isn't a lookahead just because this state is
         a consistent state with a default action.  There might have
         been a previous inconsistent state, consistent state with a
         non-default action, or user semantic action that manipulated
         yyla.  (However, yyla is currently not documented for users.)
       - Of course, the expected token list depends on states to have
         correct lookahead information, and it depends on the parser not
         to perform extra reductions after fetching a lookahead from the
         scanner and before detecting a syntax error.  Thus, state
         merging (from LALR or IELR) and default reductions corrupt the
         expected token list.  However, the list is correct for
         canonical LR with one exception: it will still contain any
         token that will not be accepted due to an error action in a
         later state.
    */
    if (yytoken != yyempty_)
      {
        yyarg[yycount++] = yytname_[yytoken];
        int yyn = yypact_[yystate];
        if (!yy_pact_value_is_default_ (yyn))
          {
            /* Start YYX at -YYN if negative to avoid negative indexes in
               YYCHECK.  In other words, skip the first -YYN actions for
               this state because they are default actions.  */
            int yyxbegin = yyn < 0 ? -yyn : 0;
            // Stay within bounds of both yycheck and yytname.
            int yychecklim = yylast_ - yyn + 1;
            int yyxend = yychecklim < yyntokens_ ? yychecklim : yyntokens_;
            for (int yyx = yyxbegin; yyx < yyxend; ++yyx)
              if (yycheck_[yyx + yyn] == yyx && yyx != yyterror_
                  && !yy_table_value_is_error_ (yytable_[yyx + yyn]))
                {
                  if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                    {
                      yycount = 1;
                      break;
                    }
                  else
                    yyarg[yycount++] = yytname_[yyx];
                }
          }
      }

    char const* yyformat = YY_NULLPTR;
    switch (yycount)
      {
#define YYCASE_(N, S)                         \
        case N:                               \
          yyformat = S;                       \
        break
        YYCASE_(0, YY_("syntax error"));
        YYCASE_(1, YY_("syntax error, unexpected %s"));
        YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
        YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
        YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
        YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
#undef YYCASE_
      }

    // Argument number.
    size_t yyi = 0;
    for (char const* yyp = yyformat; *yyp; ++yyp)
      if (yyp[0] == '%' && yyp[1] == 's' && yyi < yycount)
        {
          yyres += yytnamerr_ (yyarg[yyi++]);
          ++yyp;
        }
      else
        yyres += *yyp;
    return yyres;
  }


  const signed char bp::yypact_ninf_ = -70;

  const signed char bp::yytable_ninf_ = -1;

  const signed char
  bp::yypact_[] =
  {
       4,     9,    48,    78,    66,   -70,     2,     4,   -70,    58,
     -20,   -70,    51,   -70,   -70,    53,   -70,    61,    -1,   -70,
     -70,   -70,   -70,    66,   -70,   -10,   -70,     9,    54,    62,
       7,   -70,    52,    -7,   -70,   -70,   -70,   -70,   -70,   -70,
      84,    -6,   -70,    53,    27,    56,    57,   -70,   -70,   -70,
     -70,   -70,    60,    59,    63,    33,    86,    64,    65,    67,
      68,    69,   -70,     0,   -70,   -17,   -70,   -70,    70,    33,
     -70,    33,   -70,   -70,   -70,    33,   -70,    -4,    76,    71,
      79,    43,    20,   -70,   -70,    75,   -70,   -70,   -70,   -70,
     -70,    27,    27,    33,    80,   -70,    39,    24,    26,    37,
      88,    33,    33,    33,    33,    33,    33,   -70,    73,   -70,
     -70,   -13,    81,   -70,   -70,    82,    83,    85,   -70,    90,
      25,    71,    79,    43,   -70,   -70,   -70,    33,   -70,    33,
     -70,   -70,   -70,    87,    33,    38,    81,    96,    76,   -70,
      89,   -70
  };

  const unsigned char
  bp::yydefact_[] =
  {
       0,     0,     0,     0,     3,     4,     0,     0,    14,    19,
       0,    17,     0,     1,     5,     0,    30,     0,     0,     9,
      11,    12,    13,     2,    15,     0,    16,     0,     0,    25,
       0,    23,     0,     0,     8,     6,    10,    20,    21,    18,
       0,     0,    22,     0,     0,     0,     0,     7,    26,    27,
      24,    36,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    49,    31,    32,     0,    28,    29,     0,     0,
      35,     0,    70,    71,    72,     0,    66,     0,    55,    57,
      59,    61,     0,    63,    67,     0,    44,    45,    46,    48,
      47,     0,     0,     0,     0,    53,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,    68,     0,    33,
      34,     0,    51,    50,    37,     0,     0,     0,    69,     0,
       0,    58,    60,    62,    64,    65,    43,     0,    38,     0,
      54,    42,    41,     0,     0,     0,    52,     0,    56,    39,
       0,    40
  };

  const signed char
  bp::yypgoto_[] =
  {
     -70,   -70,   104,     6,   -70,   -70,   -70,    77,   -70,   105,
     -70,    93,   -70,   -70,    91,   -70,   -70,   -70,   -70,   -18,
     -70,   -70,   -70,   -70,   -69,   -21,    12,    13,    18,   -70,
     -30,    41
  };

  const signed char
  bp::yydefgoto_[] =
  {
      -1,     3,     4,     5,     6,    35,    18,    19,     7,     8,
      10,    11,    20,    30,    31,    21,    22,    32,    63,    64,
      68,    65,   111,    96,    77,    78,    79,    80,    81,    82,
      83,    84
  };

  const unsigned char
  bp::yytable_[] =
  {
      97,   127,    98,    34,    15,    93,    99,    15,   100,     1,
      14,    37,    26,    27,    45,    48,    94,     2,    38,   128,
     129,    46,    49,   101,   112,    91,    92,    16,    17,    14,
      16,    17,   120,    51,    52,    53,    54,    55,     9,    42,
      43,    72,    56,    57,    58,    59,    60,    61,    73,    74,
      75,   101,   101,   101,    72,   116,    62,   117,   135,   134,
     136,    73,    74,    75,   101,   101,   105,   106,   118,    76,
     139,   114,   115,   109,   110,   124,   125,    12,    13,     2,
      25,    28,    29,    33,    41,    40,    44,    47,    66,    67,
      69,    70,    85,    71,   119,    36,    86,    87,    95,    88,
      89,    90,   102,   108,   104,   126,   103,   140,   101,   113,
     130,    23,    24,   138,   121,   131,   122,   132,   133,   137,
      39,   141,   123,   107,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    50
  };

  const short int
  bp::yycheck_[] =
  {
      69,    14,    71,     4,     5,    22,    75,     5,    12,     5,
       4,    21,    32,    33,    21,    21,    33,    13,    28,    32,
      33,    28,    28,    27,    93,    25,    26,    28,    29,    23,
      28,    29,   101,     6,     7,     8,     9,    10,    29,    32,
      33,    21,    15,    16,    17,    18,    19,    20,    28,    29,
      30,    27,    27,    27,    21,    31,    29,    31,   127,    34,
     129,    28,    29,    30,    27,    27,    23,    24,    31,    36,
      32,    32,    33,    91,    92,   105,   106,    29,     0,    13,
      22,    30,    29,    22,    22,    31,    34,     3,    32,    32,
      30,    32,     6,    30,     6,    18,    32,    32,    28,    32,
      32,    32,    26,    28,    25,    32,    35,    11,    27,    29,
      28,     7,     7,   134,   102,    32,   103,    32,    28,    32,
      27,    32,   104,    82,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    43
  };

  const unsigned char
  bp::yystos_[] =
  {
       0,     5,    13,    38,    39,    40,    41,    45,    46,    29,
      47,    48,    29,     0,    40,     5,    28,    29,    43,    44,
      49,    52,    53,    39,    46,    22,    32,    33,    30,    29,
      50,    51,    54,    22,     4,    42,    44,    21,    28,    48,
      31,    22,    32,    33,    34,    21,    28,     3,    21,    28,
      51,     6,     7,     8,     9,    10,    15,    16,    17,    18,
      19,    20,    29,    55,    56,    58,    32,    32,    57,    30,
      32,    30,    21,    28,    29,    30,    36,    61,    62,    63,
      64,    65,    66,    67,    68,     6,    32,    32,    32,    32,
      32,    25,    26,    22,    33,    28,    60,    61,    61,    61,
      12,    27,    26,    35,    25,    23,    24,    68,    28,    56,
      56,    59,    61,    29,    32,    33,    31,    31,    31,     6,
      61,    63,    64,    65,    67,    67,    32,    14,    32,    33,
      28,    32,    32,    28,    34,    61,    61,    32,    62,    32,
      11,    32
  };

  const unsigned char
  bp::yyr1_[] =
  {
       0,    37,    38,    38,    39,    39,    40,    41,    42,    43,
      43,    44,    44,    44,    45,    45,    46,    47,    47,    48,
      48,    48,    49,    50,    50,    51,    51,    51,    52,    52,
      54,    53,    55,    55,    55,    56,    57,    56,    56,    56,
      56,    56,    56,    56,    56,    56,    56,    56,    56,    58,
      58,    59,    59,    60,    60,    61,    61,    62,    62,    63,
      63,    64,    64,    65,    65,    65,    66,    67,    67,    68,
      68,    68,    68
  };

  const unsigned char
  bp::yyr2_[] =
  {
       0,     2,     2,     1,     1,     2,     3,     5,     1,     1,
       2,     1,     1,     1,     1,     2,     3,     1,     3,     1,
       3,     3,     3,     1,     3,     1,     3,     3,     4,     4,
       0,     4,     1,     3,     3,     2,     0,     4,     4,     6,
       8,     5,     5,     4,     2,     2,     2,     2,     2,     1,
       3,     1,     3,     1,     3,     1,     5,     1,     3,     1,
       3,     1,     3,     1,     3,     3,     1,     1,     2,     3,
       1,     1,     1
  };



  // YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
  // First, the terminals, then, starting at \a yyntokens_, nonterminals.
  const char*
  const bp::yytname_[] =
  {
  "$end", "error", "$undefined", "\"begin\"", "\"end\"", "\"decl\"",
  "\"goto\"", "\"assume\"", "\"skip\"", "\"assert\"", "\"if\"", "\"fi\"",
  "\"then\"", "\"void\"", "\"constrain\"", "\"start_thread\"",
  "\"end_thread\"", "\"atomic_begin\"", "\"atomic_end\"", "\"wait\"",
  "\"broadcast\"", "\"*\"", "\":=\"", "\"=\"", "\"!=\"", "\"&&\"",
  "\"||\"", "\"?\"", "T_INT", "T_IDEN", "'('", "')'", "';'", "','", "':'",
  "'^'", "'!'", "$accept", "prog", "funclist", "function", "funchead",
  "funcend", "funcbody", "funcstmt", "s_decllist", "s_declstmt",
  "s_id_list", "s_id", "l_declstmt", "l_id_list", "l_id", "initistmt",
  "labelstmt", "$@1", "statement", "metastmt", "$@2", "iden_list",
  "expr_list", "to_line_list", "expr", "or_expr", "xor_expr", "and_expr",
  "equ_expr", "una_op", "una_expr", "prm_expr", YY_NULLPTR
  };

#if YYDEBUG
  const unsigned short int
  bp::yyrline_[] =
  {
       0,   103,   103,   104,   107,   108,   111,   113,   115,   117,
     118,   121,   122,   123,   127,   128,   131,   134,   135,   138,
     144,   150,   159,   162,   163,   166,   172,   178,   188,   192,
     198,   198,   208,   209,   210,   213,   216,   216,   220,   226,
     233,   237,   242,   246,   249,   252,   255,   258,   261,   266,
     270,   276,   280,   286,   289,   295,   296,   301,   302,   305,
     306,   309,   310,   313,   314,   315,   318,   321,   322,   325,
     326,   327,   328
  };

  // Print the state stack on the debug stream.
  void
  bp::yystack_print_ ()
  {
    *yycdebug_ << "Stack now";
    for (stack_type::const_iterator
           i = yystack_.begin (),
           i_end = yystack_.end ();
         i != i_end; ++i)
      *yycdebug_ << ' ' << i->state;
    *yycdebug_ << std::endl;
  }

  // Report on the debug stream that the rule \a yyrule is going to be reduced.
  void
  bp::yy_reduce_print_ (int yyrule)
  {
    unsigned int yylno = yyrline_[yyrule];
    int yynrhs = yyr2_[yyrule];
    // Print the symbols being reduced, and their result.
    *yycdebug_ << "Reducing stack by rule " << yyrule - 1
               << " (line " << yylno << "):" << std::endl;
    // The symbols being reduced.
    for (int yyi = 0; yyi < yynrhs; yyi++)
      YY_SYMBOL_PRINT ("   $" << yyi + 1 << " =",
                       yystack_[(yynrhs) - (yyi + 1)]);
  }
#endif // YYDEBUG

  // Symbol number corresponding to token number t.
  inline
  bp::token_number_type
  bp::yytranslate_ (int t)
  {
    static
    const token_number_type
    translate_table[] =
    {
     0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    36,     2,     2,     2,     2,     2,     2,
      30,    31,     2,     2,    33,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,    34,    32,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,    35,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29
    };
    const unsigned int user_token_number_max_ = 284;
    const token_number_type undef_token_ = 2;

    if (static_cast<int>(t) <= yyeof_)
      return yyeof_;
    else if (static_cast<unsigned int> (t) <= user_token_number_max_)
      return translate_table[t];
    else
      return undef_token_;
  }


} // yy
#line 1484 "bopp.tab.cc" // lalr1.cc:1155
#line 336 "bopp.y" // lalr1.cc:1156


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
