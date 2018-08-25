/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BTORSLVPROP_H_INCLUDED
#define BTORSLVPROP_H_INCLUDED

#include "btorbv.h"
#include "btorproputils.h"
#include "btorslv.h"
#include "btortypes.h"
#include "utils/btorhashint.h"

struct BtorPropSolver
{
  BTOR_SOLVER_STRUCT;

  /* Map, maintains the roots.
   * Maps root to 'selected' (= how often it got selected) */
  BtorIntHashTable *roots;

  /* Map, maintains SLS score.
   * Maps node to its SLS score, only used for heuristically selecting
   * a root r based on maximizing
   *   score(r) + BTOR_PROP_SELECT_CFACT * sqrt (log (selected(r)) / nmoves)
   * if BTOR_OPT_PROP_USE_BANDIT is enabled. */
  BtorIntHashTable *score;

  /* Work stack, maintains entailed propagations that need to be processed
   * with higher priority if BTOR_OPT_PROP_ENTAILED.
   *
   * A recoverable conflict entails that starting from the node where the
   * conflict occurred there are more paths to fix (in our case exactly one
   * other path since all bv operators are binary). These so-called entailed
   * propagations are pushed onto stack 'toprop'.
   */
  BtorPropInfoStack toprop;

#ifndef NDEBUG
  BtorPropInfoStack prop_path;
#endif

  /* current probability for selecting the cond when either the
   * 'then' or 'else' branch is const (path selection) */
  uint32_t flip_cond_const_prob;
  /* current delta for updating the probability for selecting the cond
   * when either the 'then' or 'else' branch is const (path selection) */
  int32_t flip_cond_const_prob_delta;
  /* number of times the cond has already been selected when either
   * the 'then' or 'else' branch is const */
  uint32_t nflip_cond_const;

  struct
  {
    /* Number of restarts (if BTOR_OPT_PROP_USE_RESTARTS). */
    uint32_t restarts;
    /* Number of moves. */
    uint32_t moves;
    /* Number of moves that were a consequence of entailed propagations from
     * recoverable conflicts. */
    uint32_t moves_entailed;
    /* Number of recoverable conflicts.
     * A recoverable conflict is a conflict that does not involve bit-vector
     * constants. */
    uint32_t rec_conf;
    /* Number of non-recoverable conflicts.
     * A non-recoverable conflict involves bit-vector constants. */
    uint32_t non_rec_conf;
    /* Number of recoverable conflicts that were fixed. */
    uint64_t fixed_conf;
    /* Number of propagations (total). */
    uint64_t props;
    /* Number of propagations via consistent value computation. */
    uint64_t props_cons;
    /* Number of propagataions via inverse value computation. */
    uint64_t props_inv;
    /* Number of entailed propagations. */
    uint64_t props_entailed;
    /* Number of updates performed when updating the cone of influence in the
     * current assignment as a consequence of a move. */
    uint64_t updates;

#ifndef NDEBUG
    /* Number of calls to inverse value computation functions. */
    uint32_t inv_add;
    uint32_t inv_and;
    uint32_t inv_eq;
    uint32_t inv_ult;
    uint32_t inv_sll;
    uint32_t inv_srl;
    uint32_t inv_mul;
    uint32_t inv_udiv;
    uint32_t inv_urem;
    uint32_t inv_concat;
    uint32_t inv_slice;
    uint32_t inv_cond;

    /* Number of calls to consistent value computation functions. */
    uint32_t cons_add;
    uint32_t cons_and;
    uint32_t cons_eq;
    uint32_t cons_ult;
    uint32_t cons_sll;
    uint32_t cons_srl;
    uint32_t cons_mul;
    uint32_t cons_udiv;
    uint32_t cons_urem;
    uint32_t cons_concat;
    uint32_t cons_slice;
    uint32_t cons_cond;
#endif
  } stats;

  struct
  {
    double update_cone;
    double update_cone_reset;
    double update_cone_model_gen;
    double update_cone_compute_score;
  } time;
};

typedef struct BtorPropSolver BtorPropSolver;

#define BTOR_PROP_SOLVER(btor) ((BtorPropSolver *) (btor)->slv)

BtorSolver *btor_new_prop_solver (Btor *btor);

/*------------------------------------------------------------------------*/

#endif
