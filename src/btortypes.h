/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2016 Mathias Preiner.
 *  Copyright (C) 2016-2018 Aina Niemetz.
 *  Copyright (C) 2016 Armin Biere.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORTYPES_H_INCLUDED
#define BTORTYPES_H_INCLUDED

typedef struct Btor Btor;
typedef struct BtorNode BtorNode;

enum BtorSolverResult
{
  BTOR_RESULT_SAT     = 10,
  BTOR_RESULT_UNSAT   = 20,
  BTOR_RESULT_UNKNOWN = 0,
};

typedef enum BtorSolverResult BtorSolverResult;

/* public API types */
typedef struct BoolectorNode BoolectorNode;

typedef struct BoolectorAnonymous BoolectorAnonymous;

typedef BoolectorAnonymous* BoolectorSort;

/* --------------------------------------------------------------------- */

/* Boolector options */

enum BtorOption
{
  /* --------------------------------------------------------------------- */
  /*!
    **General Options:**
   */
  /* --------------------------------------------------------------------- */
  /*!
    * **BTOR_OPT_MODEL_GEN**

      | Enable (``value``: 1 or 2) or disable (``value``: 0) generation of a
        model for satisfiable instances.
      | There are two modes for model generation:

      * generate model for asserted expressions only (``value``: 1)
      * generate model for all expressions (``value``: 2)
  */
  BTOR_OPT_MODEL_GEN,

  /*!
    * **BTOR_OPT_INCREMENTAL**

      | Enable (``value``: 1) incremental mode.
      | Note that incremental usage turns off some optimization techniques.
        Disabling incremental usage is currently not supported.
  */
  BTOR_OPT_INCREMENTAL,

  /*!
    * **BTOR_OPT_INCREMENTAL_SMT1**

      | Incremental mode for SMT1. Stop after first satisfiable formula
        (``value``: 1) or solve all formulas (``value``: 2).
      | Note that currently, incremental mode while parsing an input file is
        only supported for `SMT-LIB v1`_ input.
  */
  BTOR_OPT_INCREMENTAL_SMT1,

  /*!
    * **BTOR_OPT_INPUT_FORMAT**

      | Force input file format (``value``:
        `BTOR
         <http://fmv.jku.at/papers/BrummayerBiereLonsing-BPR08.pdf>`_:
         BTOR_INPUT_FORMAT_BTOR,
        `BTOR2
         <http://fmv.jku.at/papers/NiemetzPreinerWolfBiere-CAV18.pdf>`_:
         BTOR_INPUT_FORMAT_BTOR2 ,
        `SMT-LIB v1
         <http://smtlib.cs.uiowa.edu/papers/format-v1.2-r06.08.30.pdf>`_:
         BTOR_INPUT_FORMAT_SMT1,
        `SMT-LIB v2
         <http://smtlib.cs.uiowa.edu/papers/
          smt-lib-reference-v2.0-r12.09.09.pdf>`_:
          BTOR_INPUT_FORMAT_SMT2)
         when parsing an input file.
      | If unspecified, Boolector automatically detects the input file format
        while parsing.
  */

  BTOR_OPT_INPUT_FORMAT,
  /*!
    * **BTOR_OPT_OUTPUT_NUMBER_FORMAT**

      | Force output number format (``value``: binary: 0, hexadecimal: 1,
        decimal: 2).
      | Boolector uses binary by default.
  */
  BTOR_OPT_OUTPUT_NUMBER_FORMAT,

  /*!
    * **BTOR_OPT_OUTPUT_FORMAT**

      | Force output file format (``value``: BTOR_: -1, `SMT-LIB v1`_: 1,
        `SMT-LIB v2`_: 2).
      | Boolector uses BTOR_ by default.
  */
  BTOR_OPT_OUTPUT_FORMAT,

  /*!
    * **BTOR_OPT_ENGINE**

      | Set solver engine (``value``: BTOR_ENGINE_FUN: 0, BTOR_ENGINE_SLS: 1,
        BTOR_ENGINE_PROP: 2).
      | Boolector uses BTOR_ENGINE_FUN by default.
  */
  BTOR_OPT_ENGINE,

  /*!
    * **BTOR_OPT_SAT_ENGINE**

      | Set sat solver engine (``value``: BTOR_SAT_ENGINE_LINGELING,
        BTOR_SAT_ENGINE_PICOSAT, BTOR_SAT_ENGINE_MINISAT).
      | Available option values and default values depend on the sat solvers
        configured.
  */
  BTOR_OPT_SAT_ENGINE,

  /*!
    * **BTOR_OPT_AUTO_CLEANUP**

      Enable (``value``:1) or disable (``value``:0) auto cleanup of all
      references held on exit.
    */
  BTOR_OPT_AUTO_CLEANUP,

  /*!
    * **BTOR_OPT_PRETTY_PRINT**

      Enable (``value``: 1) or disable (``value``: 0) pretty printing when
      dumping.
  */
  BTOR_OPT_PRETTY_PRINT,

  /*!
    * **BTOR_OPT_EXIT_CODES**

      | Enable (``value``:1) or disable (``value``:0) the use of Boolector exit
        codes (BOOLECTOR_SAT, BOOLECTOR_UNSAT, BOOLECTOR_UNKNOWN - see
        :ref:`macros`).
      | If disabled, on exit Boolector returns 0 if success (sat or unsat), and
        1 in any other case.
  */
  BTOR_OPT_EXIT_CODES,

  /*!
    * **BTOR_OPT_SEED**

      | Set seed for Boolector's internal random number generator.
      | Boolector uses 0 by default.
  */
  BTOR_OPT_SEED,

  /*
    * **BTOR_OPT_VERBOSITY**

      Set the level of verbosity.
  */
  BTOR_OPT_VERBOSITY,

  /*
    * **BTOR_OPT_LOGLEVEL**

      Set the log level.
  */
  BTOR_OPT_LOGLEVEL,

  /* --------------------------------------------------------------------- */
  /*!
    **Simplifier Options:**
   */
  /* --------------------------------------------------------------------- */

  /*!
    * **BTOR_OPT_REWRITE_LEVEL**

      | Set the rewrite level (``value``: 0-3) of the rewriting engine.
      | Boolector uses rewrite level 3 by default, rewrite levels are
        classified as follows:

      * 0: no rewriting
      * 1: term level rewriting
      * 2: more simplification techniques
      * 3: full rewriting/simplification

      | Do not alter the rewrite level of the rewriting engine after creating
        expressions.
  */
  BTOR_OPT_REWRITE_LEVEL,

  /*!
    * **BTOR_OPT_SKELETON_PREPROC**

      Enable (``value``: 1) or disable (``value``: 0) skeleton  preprocessing
      during simplification.
  */
  BTOR_OPT_SKELETON_PREPROC,

  /*!
    * **BTOR_OPT_ACKERMANN**

      Enable (``value``: 1) or disable (``value``: 0) the eager addition of
      Ackermann constraints for function applications.
  */
  BTOR_OPT_ACKERMANN,

  /*!
    * **BTOR_OPT_BETA_REDUCE_ALL**

      Enable (``value``: 1) or disable (``value``: 0) the eager elimination of
      lambda expressions via beta reduction.
  */
  BTOR_OPT_BETA_REDUCE_ALL,

  /*!
    * **BTOR_OPT_ELIMINATE_SLICES**

      Enable (``value``: 1) or disable (``value``: 0) slice elimination on bit
      vector variables.
  */
  BTOR_OPT_ELIMINATE_SLICES,

  /*!
    * **BTOR_OPT_VAR_SUBST**

      Enable (``value``: 1) or disable (``value``: 0) variable substitution
      during simplification.
  */
  BTOR_OPT_VAR_SUBST,

  /*!
    * **BTOR_OPT_UCOPT**

      Enable (``value``: 1) or disable (``value``: 0) unconstrained
      optimization.
  */
  BTOR_OPT_UCOPT,

  /*!
    * **BTOR_OPT_MERGE_LAMBDAS**

      Enable (``value``: 1) or disable (``value``: 0) merging of lambda
      expressions.
  */
  BTOR_OPT_MERGE_LAMBDAS,

  /*!
    * **BTOR_OPT_EXTRACT_LAMBDAS**

      Enable (``value``: 1) or disable (``value``: 0) extraction of common
      array patterns as lambda terms.
  */
  BTOR_OPT_EXTRACT_LAMBDAS,

  /*!
    * **BTOR_OPT_NORMALIZE**

      Enable (``value``: 1) or disable (``value``: 0) normalization of
      addition, multiplication and bit-wise and.
  */
  BTOR_OPT_NORMALIZE,

  /*!
    * **BTOR_OPT_NORMALIZE_ADD**

      Enable (``value``: 1) or disable (``value``: 0) normalization of
      addition.
  */
  BTOR_OPT_NORMALIZE_ADD,

  /* --------------------------------------------------------------------- */
  /*!
    **Fun Engine Options:**
   */
  /* --------------------------------------------------------------------- */

  /*!
    * **BTOR_OPT_FUN_PREPROP**

      Enable (``value``: 1) or disable (``value``: 0) prop engine as
      preprocessing step within sequential portfolio setting.
   */
  BTOR_OPT_FUN_PREPROP,

  /*!
    * **BTOR_OPT_FUN_PRESLS**

      Enable (``value``: 1) or disable (``value``: 0) sls engine as
      preprocessing step within sequential portfolio setting.
   */
  BTOR_OPT_FUN_PRESLS,

  /*!
    * **BTOR_OPT_FUN_DUAL_PROP**

      Enable (``value``: 1) or disable (``value``: 0) dual propagation
      optimization.
  */
  BTOR_OPT_FUN_DUAL_PROP,

  /*!
    * **BTOR_OPT_FUN_DUAL_PROP_QSORT**

      | Set order in which inputs are assumed in dual propagation clone.
      | Boolector uses BTOR_DP_QSORT_JUST by default.

      * BTOR_DP_QSORT_JUST (0): order by score, highest score first
      * BTOR_DP_QSORT_ASC (1): order by input id, ascending
      * BTOR_DP_QSORT_DESC (2): order by input id, descending
  */
  BTOR_OPT_FUN_DUAL_PROP_QSORT,

  /*!
    * **BTOR_OPT_FUN_JUST**

      Enable (``value``: 1) or disable (``value``: 0) justification
      optimization.
  */
  BTOR_OPT_FUN_JUST,

  /*!
    * **BTOR_OPT_FUN_JUST_HEURISTIC**

      | Set heuristic that determines path selection for justification
        optimization.
      | Boolector uses BTOR_JUST_HEUR_BRANCH_MIN_APP by default.

      * BTOR_JUST_HEUR_LEF (0): always choose left branch
      * BTOR_JUST_HEUR_BRANCH_MIN_APP (1): choose branch with minimum number of
        applies
      * BTOR_JUST_HEUR_BRANCH_MIN_DEP (2): choose branch with minimum depth
  */
  BTOR_OPT_FUN_JUST_HEURISTIC,

  /*!
    * **BTOR_OPT_FUN_LAZY_SYNTHESIZE**

      Enable (``value``: 1) or disable (``value``: 0) lazy synthesis of bit
      vector expressions.
  */
  BTOR_OPT_FUN_LAZY_SYNTHESIZE,

  /*!
    * **BTOR_OPT_FUN_EAGER_LEMMAS**

      | Enable (``value``: 1) or disable (``value``: 0) eager generation
        lemmas.
      | If enabled, in each refinement iteration, lemmas for all possible
        conflicts for the candidate model are generated (rather than generating
        one single lemma per refinement iteration).
  */
  BTOR_OPT_FUN_EAGER_LEMMAS,

  BTOR_OPT_FUN_STORE_LAMBDAS,

  /* --------------------------------------------------------------------- */
  /*!
    **SLS Engine Options:**
   */
  /* --------------------------------------------------------------------- */

  /*!
    * **BTOR_OPT_SLS_NFIPS**
      Set the number of bit flips used as a limit for the sls engine. Disabled
      if 0.
   */
  BTOR_OPT_SLS_NFLIPS,

  /*!
    * **BTOR_OPT_SLS_STRATEGY**

      | Set move strategy for SLS engine.
      | Boolector uses BTOR_SLS_STRAT_BEST_MOVE by default.

      * BTOR_SLS_STRAT_BEST_MOVE (0): always choose best score improving move
      * BTOR_SLS_STRAT_RAND_WALK (1): always choose random walk weighted by
        score
      * BTOR_SLS_STRAT_FIRST_BEST_MOVE (2): always choose first best move (no
        matter if any other move is better)
      * BTOR_SLS_STRAT_BEST_SAME_MOVE (3): determine move as best move even if
        its score is not better but the same as the score of the previous best
        move
      * BTOR_SLS_STRAT_ALWAYS_PROP (4): always choose propagation move (and
        recover with SLS move in case of conflict)
  */
  BTOR_OPT_SLS_STRATEGY,

  /*!
    * **BTOR_OPT_SLS_JUST**

      Enable (``value``: 1) or disable (``value``: 0) justification based path
      selection during candidate selection.
  */
  BTOR_OPT_SLS_JUST,

  /*!
    * **BTOR_OPT_SLS_MOVE_GW**

      Enable (``value``: 1) or disable (``value``: 0) group-wise moves, where
      rather than changing the assignment of one single candidate variable, all
      candidate variables are set at the same time (using the same strategy).
  */
  BTOR_OPT_SLS_MOVE_GW,

  /*!
    * **BTOR_OPT_SLS_MOVE_RANGE**

      Enable (``value``: 1) or disable (``value``: 0) range-wise bit-flip
      moves, where the bits within all ranges from 2 to the bit width (starting
      from the LSB) are flipped at once.
  */
  BTOR_OPT_SLS_MOVE_RANGE,

  /*!
    * **BTOR_OPT_SLS_MOVE_SEGMENT**

      Enable (``value``: 1) or disable (``value``: 0) segment-wise bit-flip
      moves, where the bits within segments of multiples of 2 are flipped at
      once.
  */
  BTOR_OPT_SLS_MOVE_SEGMENT,

  /*!
    * **BTOR_OPT_SLS_MOVE_RAND_WALK**

      Enable (``value``: 1) or disable (``value``: 0) random walk moves, where
      one out of all possible neighbors is randomly selected (with given
      probability, see BTOR_OPT_SLS_PROB_MOVE_RAND_WALK) for a randomly
      selected candidate variable.
  */
  BTOR_OPT_SLS_MOVE_RAND_WALK,

  /*!
    * **BTOR_OPT_SLS_PROB_MOVE_RAND_WALK**

      Set the probability with which a random walk is chosen if random walks
      are enabled (see BTOR_OPT_SLS_MOVE_RAND_WALK).
  */
  BTOR_OPT_SLS_PROB_MOVE_RAND_WALK,

  /*!
    * **BTOR_OPT_SLS_MOVE_RAND_ALL**

      Enable (``value``: 1) or disable (``value``: 0) the randomization of all
      candidate variables (rather than a single randomly selected candidate
      variable) in case no best move has been found.
  */
  BTOR_OPT_SLS_MOVE_RAND_ALL,

  /*!
    * **BTOR_OPT_SLS_MOVE_RAND_RANGE**

      Enable (``value``: 1) or disable (``value``: 0) the randomization of bit
      ranges (rather than all bits) of a candidate variable(s) to be randomized
      in case no best move has been found.
  */
  BTOR_OPT_SLS_MOVE_RAND_RANGE,

  /*!
    * **BTOR_OPT_SLS_MOVE_PROP**

      Enable (``value``: 1) or disable (``value``: 0) propagation moves (chosen
      with a given ratio of number of propagation moves to number of regular
      SLS moves, see BTOR_OPT_SLS_MOVE_PROP_N_PROP and
      BTOR_OPT_SLS_MOVE_PROP_N_SLS).
  */
  BTOR_OPT_SLS_MOVE_PROP,

  /*!
    * **BTOR_OPT_SLS_MOVE_PROP_N_PROP**

      Set the number of propagation moves to be performed when propagation
      moves are enabled (propagation moves are chosen with a ratio of
      propagation moves to regular SLS moves, see BTOR_OPT_SLS_MOVE_PROP and
      BTOR_OPT_SLS_MOVE_PROP_N_SLS).
  */
  BTOR_OPT_SLS_MOVE_PROP_N_PROP,

  /*!
    * **BTOR_OPT_SLS_MOVE_PROP_N_SLS**

      Set the number of regular SLS moves to be performed when propagation
      moves are enabled (propagation moves are chosen with a ratio of
      propagation moves to regular SLS moves, see BTOR_OPT_SLS_MOVE_PROP and
      BTOR_OPT_SLS_MOVE_PROP_N_PROP).
  */
  BTOR_OPT_SLS_MOVE_PROP_N_SLS,

  /*!
    * **BTOR_OPT_SLS_MOVE_PROP_FORCE_RW**

      Enable (``value``: 1) or disable (``value``: 0) that random walks are
      forcibly chosen as recovery moves in case of conflicts when a propagation
      move is performed (rather than performing a regular SLS move).
  */
  BTOR_OPT_SLS_MOVE_PROP_FORCE_RW,

  /*!
    * **BTOR_OPT_SLS_MOVE_INC_MOVE_TEST**

      Enable (``value``: 1) or disable (``value``: 0) that during best move
      selection, if the current candidate variable with a previous neighbor
      yields the currently best score, this neighbor assignment is used as a
      base for further neighborhood exploration (rather than its current
      assignment).
  */
  BTOR_OPT_SLS_MOVE_INC_MOVE_TEST,

  /*!
    * **BTOR_OPT_SLS_MOVE_RESTARTS**

      Enable (``value``: 1) or disable (``value``: 0) restarts.
  */
  BTOR_OPT_SLS_USE_RESTARTS,

  /*!
    * **BTOR_OPT_SLS_MOVE_RESTARTS**

      | Enable (``value``: 1) or disable (``value``: 0) heuristic (bandit
        scheme) for selecting root constraints.
      | If disabled, candidate root constraints are selected randomly.
  */
  BTOR_OPT_SLS_USE_BANDIT,

  /* --------------------------------------------------------------------- */
  /*!
    **Prop Engine Options**:
   */
  /* --------------------------------------------------------------------- */

  /*!
    * **BTOR_OPT_PROP_NPROPS**

      Set the number of propagation (steps) used as a limit for the propagation
      engine. Disabled if 0.
   */
  BTOR_OPT_PROP_NPROPS,

  /*!
    * **BTOR_OPT_PROP_ENTAILED**

      Maintain a work queue with entailed propagations.
      If enabled, propagations from this queue are propagated before randomly
      choosing a yet unsatisfied path from the root.

      This feature is disabled (BTOR_PROP_ENTAILED_OFF) by default.

      * BTOR_PROP_ENTAILED_OFF: do not use strategy (default)
      * BTOR_PROP_ENTAILED_ALL: propagate all entailed propagations
      * BTOR_PROP_ENTAILED_FIRST: process only the first entailed propagation
      * BTOR_PROP_ENTAILED_LAST: process only the last entailed propagation
  */
  BTOR_OPT_PROP_ENTAILED,

  /*!
    * **BTOR_OPT_PROP_USE_RESTARTS**

      Enable (``value``: 1) or disable (``value``: 0) restarts.
  */
  BTOR_OPT_PROP_USE_RESTARTS,

  /*!
    * **BTOR_OPT_PROP_USE_RESTARTS**

      | Enable (``value``: 1) or disable (``value``: 0) heuristic (bandit
        scheme) for selecting root constraints.
      | If enabled, root constraint selection via bandit scheme is based on a
        scoring scheme similar to the one employed in the SLS engine.
      | If disabled, candidate root constraints are selected randomly.
  */
  BTOR_OPT_PROP_USE_BANDIT,

  /*!
    * **BTOR_OPT_PROP_PATH_SEL**

      Choose mode for path selection.
  */
  BTOR_OPT_PROP_PATH_SEL,

  /*!
    * **BTOR_OPT_PROP_PROB_USE_INV_VALUE**

     Set probabiality with which to choose inverse values over consistent
     values.
  */
  BTOR_OPT_PROP_PROB_USE_INV_VALUE,

  /*!
    * **BTOR_OPT_PROP_PROB_FLIP_COND**

     Set probability with which to select the path to the condition (in case of
     an if-then-else operation) rather than the enabled branch during down
     propagation.
  */
  BTOR_OPT_PROP_PROB_FLIP_COND,

  /*!
    * **BTOR_OPT_PROP_PROB_FLIP_COND_CONST**

     Set probbiality with which to select the path to the condition (in case of
     an if-then-else operation) rather than the enabled branch during down
     propagation if either of the 'then' or 'else' branch is constant.
  */
  BTOR_OPT_PROP_PROB_FLIP_COND_CONST,

  /*!
    * **BTOR_OPT_PROP_FLIP_COND_CONST_DELTA**

     Set delta by which BTOR_OPT_PROP_PROB_FLIP_COND_CONST is decreased or
     increased after a limit BTOR_OPT_PROP_FLIP_COND_CONST_NPATHSEL is reached.
  */
  BTOR_OPT_PROP_FLIP_COND_CONST_DELTA,

  /*!
    * **BTOR_OPT_PROP_FLIP_COND_CONST_NPATHSEL**

     Set the limit for how often the path to the condition (in case of an
     if-then-else operation) may be selected bevor
     BTOR_OPT_PROP_PROB_FLIP_COND_CONST is decreased or increased by
     BTOR_OPT_PROP_PROB_FLIP_COND_CONST_DELTA.
  */
  BTOR_OPT_PROP_FLIP_COND_CONST_NPATHSEL,

  /*!
    * **BTOR_OPT_PROP_PROB_SLICE_KEEP_DC**

      Set probability with which to keep the current value of the don't care
      bits of a slice operation (rather than fully randomizing all of them)
      when selecting an inverse or consistent value.
   */
  BTOR_OPT_PROP_PROB_SLICE_KEEP_DC,

  /*!
    * **BTOR_OPT_PROP_PROB_CONC_FLIP**

     Set probability with which to use the corresponing slice of current
     assignment with max. one of its bits flipped (rather than using the
     corresponding slice of the down propagated assignment) as result of
     consistent value selection for concats.
  */
  BTOR_OPT_PROP_PROB_CONC_FLIP,

  /*!
    * **BTOR_OPT_PROP_PROB_SLICE_FLIP**

     Set probability with which to use the current assignment of the operand of
     a slice operation with one of the don't care bits flipped (rather than
     fully randomizing all of them, both for inverse and consistent value
     selection) if their current assignment is not kept (see
     BTOR_OPT_PROP_PROB_SLICE_KEEP_DC).
  */
  BTOR_OPT_PROP_PROB_SLICE_FLIP,

  /*!
    * **BTOR_OPT_PROP_PROB_EQ_FLIP**

     Set probability with which the current assignment of the selected node
     with one of its bits flipped (rather than a fully randomized bit-vector)
     is down-propagated in case of an inequality (both for inverse and
     consistent value selection).
  */
  BTOR_OPT_PROP_PROB_EQ_FLIP,

  /*!
    * **BTOR_OPT_PROP_PROB_AND_FLIP**

     Set probability with which the current assignment of the don't care bits
     of the selected node with max. one of its bits flipped (rather than fully
     randomizing all of them) in case of an and operation (for both inverse and
     consistent value selection).

  */
  BTOR_OPT_PROP_PROB_AND_FLIP,

  /*!
    * **BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT**

      | Do not perform a propagation move when running into a conflict during
        inverse computation.
      | (This is the default behavior for the SLS engine when propagation moves
        are enabled, where a conflict triggers a recovery by means of a regular
        SLS move.)
    */
  BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT,

  /* --------------------------------------------------------------------- */
  /*!
    **AIGProp Engine Options**:
   */
  /* --------------------------------------------------------------------- */

  /*!
    * **BTOR_OPT_AIGPROP_USE_RESTARTS**

      Enable (``value``: 1) or disable (``value``: 0) restarts.
  */
  BTOR_OPT_AIGPROP_USE_RESTARTS,

  /*!
    * **BTOR_OPT_AIGPROP_USE_RESTARTS**

      | Enable (``value``: 1) or disable (``value``: 0) heuristic (bandit
        scheme) for selecting root constraints.
      | If enabled, root constraint selection via bandit scheme is based on a
        scoring scheme similar to the one employed in the SLS engine.
      | If disabled, candidate root constraints are selected randomly.
  */
  BTOR_OPT_AIGPROP_USE_BANDIT,

  /* QUANT engine ------------------------------------------------------- */
  BTOR_OPT_QUANT_SYNTH,
  BTOR_OPT_QUANT_DUAL_SOLVER,
  BTOR_OPT_QUANT_SYNTH_LIMIT,
  BTOR_OPT_QUANT_SYNTH_ITE_COMPLETE,
  BTOR_OPT_QUANT_FIXSYNTH,
  BTOR_OPT_QUANT_SYNTH_QI,
  BTOR_OPT_QUANT_DER,
  BTOR_OPT_QUANT_CER,
  BTOR_OPT_QUANT_MINISCOPE,

  /* internal options --------------------------------------------------- */

  BTOR_OPT_DEFAULT_TO_CADICAL,
  BTOR_OPT_SORT_EXP,
  BTOR_OPT_SORT_AIG,
  BTOR_OPT_SORT_AIGVEC,
  BTOR_OPT_AUTO_CLEANUP_INTERNAL,
  BTOR_OPT_SIMPLIFY_CONSTRAINTS,
  BTOR_OPT_CHK_FAILED_ASSUMPTIONS,
  BTOR_OPT_CHK_MODEL,
  BTOR_OPT_CHK_UNCONSTRAINED,
  BTOR_OPT_PARSE_INTERACTIVE,
  BTOR_OPT_SAT_ENGINE_LGL_FORK,
  BTOR_OPT_INCREMENTAL_RW,
  BTOR_OPT_DECLSORT_BV_WIDTH,
  /* this MUST be the last entry! */
  BTOR_OPT_NUM_OPTS,
};
typedef enum BtorOption BtorOption;

/* Callback function to be executed on abort, primarily intended to be used for
 * plugging in exception handling. */
struct BtorAbortCallback
{
  void (*abort_fun) (const char* msg);
  void *cb_fun;   /* abort callback function */
};
typedef struct BtorAbortCallback BtorAbortCallback;

extern BtorAbortCallback btor_abort_callback;

#endif
