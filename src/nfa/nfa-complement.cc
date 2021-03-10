/* nfa-complement.cc -- NFA complement
 *
 * Copyright (c) 2020 Ondrej Lengal <ondra.lengal@gmail.com>
 *
 * This file is a part of libvata2.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 */

// VATA headers
#include <fstream>  //remove
#include <iostream> //remove
#include <vata2/nfa.hh>

using namespace Vata2::Nfa;
using namespace Vata2::util;

using SccTransitionMap =
    std::unordered_map<std::pair<unsigned int, unsigned int>, Nfa>;

namespace { // anonymous namespace

struct VertexInfo {
    bool visited;
    uintptr_t index;
    uintptr_t lowlink;
    bool onStack;
    StateSet post;
};

void complement_classical(
	Nfa*                result,
	const Nfa&          aut,
	const Alphabet&     alphabet,
    SubsetMap*          subset_map,
    const StringDict&   params = {})
{ // {{{
	assert(nullptr != result);

	bool delete_subset_map = false;
	if  (nullptr == subset_map)
	{
		subset_map = new SubsetMap();
		delete_subset_map = true;
	}

	State last_state_num;
	*result = determinize(aut, subset_map, &last_state_num);
	State sink_state = last_state_num + 1;
	auto it_inserted_pair = subset_map->insert({{}, sink_state});
	if (!it_inserted_pair.second)
	{
		sink_state = it_inserted_pair.first->second;
	}

	make_complete(result, alphabet, sink_state);
	std::set<State> old_fs = std::move(result->finalstates);
	result->finalstates = { };
	assert(result->initialstates.size() == 1);

	auto make_final_if_not_in_old = [&](const State& state) {
		if (!haskey(old_fs, state))
		{
			result->finalstates.insert(state);
		}
	};

	make_final_if_not_in_old(*result->initialstates.begin());

	for (const auto& tr : *result)
	{
		make_final_if_not_in_old(tr.tgt);
	}

	if (delete_subset_map)
	{
		delete subset_map;
	}
} // complement_classical }}}

void complement_classical_scc(
    Nfa*            result,
    const Nfa&      aut,
    const StateSet& ports,
    const Alphabet& alphabet,
    SubsetMap*      subset_map)
{ // {{{
    assert(nullptr != result);

    bool delete_subset_map = false;
    if (nullptr == subset_map)
    {
        subset_map = new SubsetMap();
        delete_subset_map = true;
    }

    State last_state_num;
    determinize_scc(result, aut, ports, subset_map, &last_state_num);
    State sink_state = last_state_num + 1;
    auto it_inserted_pair = subset_map->insert({{}, sink_state});
    if (!it_inserted_pair.second)
    {
        sink_state = it_inserted_pair.first->second;
    }
    StateSet determ_ports;

    for (State port_state : ports)
    {
        determ_ports.insert(subset_map->at({port_state}));
    }

    make_complete_scc(result, alphabet, determ_ports, sink_state);
    std::set<State> old_fs = std::move(result->finalstates);
    result->finalstates = {};

    auto make_final_if_not_in_old = [&](const State &state)
    {
        if (!haskey(old_fs, state))
        {
            result->finalstates.insert(state);
        }
    };

    for (const auto &tr : *result)
    {
        make_final_if_not_in_old(tr.tgt);
        make_final_if_not_in_old(tr.src);
    }

    if (delete_subset_map)
    {
        delete subset_map;
    }
} // complement_classical_scc }}}

unsigned int count_non_determinism(const Nfa& aut, StateSet* set)
{
    unsigned int result = 0;
    for (State state : *set)
    {
        auto post_symbs = aut[state];

        for (auto symb_set_pair : post_symbs)
        {
            unsigned int count = 0;
            for (State state_b : symb_set_pair.second)
            {
                if (set->find(state_b) != set->end())
                {
                    count++;
                }
            }
            if (count > 1)
            {
                result += count - 1;
            }
        }
    }
    return result;
}

unsigned int count_non_determinism(const Nfa& aut)
{
    unsigned int result = 0;
    State last_state = 0;
    Symbol last_symbol = 0;
    bool first = true;

    unsigned int count = 0;
    for (auto trans : aut)
    {
        if (first)
        {
            last_state = trans.src;
            last_symbol = trans.symb;
            first = false;
            continue;
        }

        if (trans.src == last_state && trans.symb == last_symbol)
        {
            count++;
        }
        else
        {
            last_state = trans.src;
            last_symbol = trans.symb;
            result += count;
            count = 0;
        }
    }

    return result;
}

void complement_reverted(
    Nfa*                result,
    const Nfa&          aut,
    const Alphabet&     alphabet,
    SubsetMap*          subset_map,
    const StringDict&   params = {})
{ // {{{
    assert(nullptr != result);

    bool delete_subset_map = false;
    if (nullptr == subset_map)
    {
        subset_map = new SubsetMap();
        delete_subset_map = true;
    }

    Nfa reverted_aut = revert(aut);

    Nfa complement;
    complement_classical(&complement, reverted_aut, alphabet, subset_map);

    assert(is_complete(complement, alphabet));

    *result = revert(complement);

} // complement_reverse }}}

void complement_reverted_min(
    Nfa*                result,
    const Nfa&          aut,
    const Alphabet&     alphabet,
    SubsetMap*          subset_map,
    const StringDict&   params = {})
{ // {{{
    assert(nullptr != result);

    bool delete_subset_map = false;
    if (nullptr == subset_map)
    {
        subset_map = new SubsetMap();
        delete_subset_map = true;
    }

    Nfa reverted_aut = revert(aut);

    Nfa complement;
    complement_classical(&complement, reverted_aut, alphabet, subset_map);

    // minimize
    Nfa tmp = revert(complement);
    tmp = determinize(tmp);
    tmp = revert(tmp);
    State last_state_num;
    tmp = determinize(tmp, subset_map, &last_state_num);
    State sink_state = last_state_num + 1;
    auto it_inserted_pair = subset_map->insert({{}, sink_state});
    if (!it_inserted_pair.second) {
        sink_state = it_inserted_pair.first->second;
    }

    make_complete(&tmp, alphabet, sink_state);

    assert(is_complete(tmp, alphabet));

    *result = revert(tmp);

} // complement_reverse }}}

void complement_choose_better(
    Nfa*                result,
    const Nfa&          aut,
    const Alphabet&     alphabet,
    SubsetMap*          subset_map,
    const StringDict&   params = {})
{ // {{{
    assert(nullptr != result);

    Nfa aut_reverted = revert(aut);

    unsigned int count_forward = count_non_determinism(aut);
    unsigned int count_backward = count_non_determinism(aut_reverted);

    if (count_forward <= count_backward) {
        complement_classical(result, aut, alphabet, subset_map);
    }
    else {
        complement_reverted(result, aut, alphabet, subset_map);
    }

} // complement_choose_better }}}

void strong_connect(
    State                                   vertex,
    uintptr_t&                              index,
    std::stack<State>&                      stack,
    std::unordered_map<State, VertexInfo>&  states,
    std::vector<StateSet>&                  result)
{
    VertexInfo *v_info = &states[vertex];
    v_info->index = index;
    v_info->lowlink = index;
    v_info->onStack = true;
    v_info->visited = true;
    stack.push(vertex);
    ++index;

    for (auto wertex : v_info->post)
    {
        VertexInfo* w_info = &states[wertex];
        if (w_info->visited == false)
        {
            // std::cout << "from: "<<vertex << " to " << wertex <<"\n";
            strong_connect(wertex, index, stack, states, result);
            v_info->lowlink = std::min(v_info->lowlink, w_info->lowlink);
        }
        else if (w_info->onStack)
        {

            v_info->lowlink = std::min(v_info->lowlink, w_info->index);
        }
    }
    State wertex = stack.top();

    if (v_info->index == v_info->lowlink)
    {
        StateSet scc;

        do
        {
            wertex = stack.top();
            stack.pop();
            VertexInfo* w_info = &states[wertex];
            w_info->onStack = false;
            scc.insert(wertex);
        } while (wertex != vertex);
        result.push_back(scc);
    }
}

void scc_tarjan(std::vector<StateSet>& result, const Nfa& aut)
{ // {{{

    uintptr_t index = 0;
    std::unordered_map<State, VertexInfo> states;
    std::stack<State> stack;

    for (auto trans : aut)
    {
        if (states.find(trans.src) == states.end())
        {
            VertexInfo info;
            info.visited = false;
            info.post.insert(trans.tgt);
            states.insert({trans.src, info});
        }
        else
        {
            VertexInfo* v_info = &states.find(trans.src)->second;
            v_info->post.insert(trans.tgt);
        }
        if (states.find(trans.tgt) == states.end())
        {
            VertexInfo info;
            info.visited = false;
            states.insert({trans.tgt, info});
        }
    }

    for (auto state : states)
    {
        if (state.second.visited == false)
        {
            StateSet scc;
            strong_connect(state.first, index, stack, states, result);
        }
    }

} // scc_tarjan }}}

std::vector<StateSet> multiplyVector(std::vector<StateSet> vs, StateSet* set)
{
    if (set->empty())
    {
        return std::vector<StateSet>();
    }

    std::vector<StateSet> new_big;

    for (State x : *set)
    {
        auto new_vector = vs;
        for (auto& y : new_vector)
        {
            y.insert(x);
        }

        new_big.insert(new_big.end(), new_vector.begin(), new_vector.end());
    }

    return new_big;
}

void remove_little_brothers(std::vector<StateSet>* vs)
{
    std::sort(vs->begin(), vs->end(), [](const StateSet& a, const StateSet& b)
    {
        return a.size() < b.size();
    });

    for (unsigned long i = 0; i < vs->size(); i++)
    {
        for (unsigned long j = i + 1; j < vs->size(); j++)
        {
            if (is_subset(vs->at(i), vs->at(j)))
            {
                vs->erase(vs->begin() + j);
            }
        }
    }
}

// DEBUG
void find_the_bad_transition(Nfa aut)
{
    State state_from = 1;
    Symbol symbol = 97;
    State state_to = 2;

    auto post_state = aut[state_from];
    auto post_symbol = post_state[symbol];

    if (post_symbol.find(state_to) != post_symbol.end())
    {
        std::cerr << "its here\n";
    }
    else {
        std::cerr << "not here\n";
    }
}

void complement_concat(
    Nfa*            result,
    const Nfa&      aut_determinized,
    const Nfa&      aut_complement,
    const Alphabet& alphabet,
    StateSetMap*    state_subset_map)
{ // {{{

    bool delete_subset_map = false;
    if (nullptr == state_subset_map)
    {
        state_subset_map = new StateSetMap();
        delete_subset_map = true;
    }

    State cnt_state = 0;
    std::list<std::pair<const StateStateSetPair *, State>> worklist;

    if (!are_disjoint(aut_determinized.initialstates, aut_determinized.finalstates))
    {
        for (auto state : aut_complement.initialstates)
        {
            StateSet set;
            set.insert(state);
            StateStateSetPair pair = std::make_pair(*aut_determinized.initialstates.begin(), set);
            auto it_bool_pair = state_subset_map->insert({pair, cnt_state});
            result->initialstates.insert(cnt_state);
            worklist.push_back({&it_bool_pair.first->first, cnt_state});
            ++cnt_state;
        }
    }
    else {
        StateSet set;
        StateStateSetPair pair = std::make_pair(*aut_determinized.initialstates.begin(), set);
        auto it_bool_pair = state_subset_map->insert({pair, cnt_state});
        result->initialstates = {cnt_state};
        worklist.push_back({&it_bool_pair.first->first, cnt_state});
        ++cnt_state;
    }

    while (!worklist.empty())
    {
        const StateStateSetPair *state_state_set;
        State new_state;
        tie(state_state_set, new_state) = worklist.front();
        worklist.pop_front();
        assert(nullptr != state_state_set);

        // set the state final
        if (is_subset(state_state_set->second, aut_complement.finalstates))
        {
            result->finalstates.insert(new_state);
        }

        PostSymb post_determinized = aut_determinized[state_state_set->first];
        std::unordered_map<State, std::vector<StateSet>> post_complement;

        for (auto symb_set : post_determinized)
        {
            std::vector<StateSet> list;
            list.push_back(StateSet());
            for (State s : state_state_set->second) {
                StateSet next_set_complement;
                if (aut_complement[s].find(symb_set.first) != aut_complement[s].end())
                {
                    next_set_complement = aut_complement[s].at(symb_set.first);
                    list = multiplyVector(list, &next_set_complement);
                }
                else
                {
                    list = std::vector<StateSet>();
                    break;
                }
            }

            if (aut_determinized.has_final(*symb_set.second.begin()))
            {
                auto initial_states = aut_complement.initialstates;
                list = multiplyVector(list, &initial_states);
            }

            remove_little_brothers(&list);

            post_complement.insert({symb_set.first, list});
        }

        for (auto x : post_determinized)
        {
            Symbol symbol = x.first;
            State state_determized = *x.second.begin();

            auto vector_complement = post_complement.at(symbol);

            for (auto set_complement : vector_complement)
            {
                auto pair = std::make_pair(state_determized, set_complement);
                auto it_bool_pair = state_subset_map->insert({pair, cnt_state});
                if (it_bool_pair.second)
                {
                    worklist.push_back({&it_bool_pair.first->first, cnt_state});
                    cnt_state++;
                }

                State post_state = it_bool_pair.first->second;
                result->add_trans(new_state, symbol, post_state);
            }
        }
    }

    if (delete_subset_map) {
        delete state_subset_map;
    }

} // complement_concat }}}

// creates automata containing only states from set
void automata_from_set(Nfa* result, const Nfa& aut, StateSet set)
{
    for (State state : set)
    {
        if (aut.has_initial(state))
        {
            result->add_initial(state);
        }
    }

    for (State state : set)
    {
        if (aut.has_final(state))
        {
            result->add_final(state);
        }
    }

    for (State state_src : set)
    {
        PostSymb post_symb = aut[state_src];
        for (const auto &symb_set : post_symb)
        {
            for (State state_tgt : symb_set.second)
            {
                if (haskey(set, state_tgt))
                {
                    result->add_trans(state_src, symb_set.first, state_tgt);
                }
            }
        }
    }
}

void create_in_map(InMap& in_map, SubsetMap& subset_map, const StateSet& ports)
{
    for (State port : ports)
    {
        State new_port = subset_map[{port}];
        in_map[port] = {new_port};
    }
}

void create_in_map_reverse(
    InMap&          in_map,
    SubsetMap&      subset_map,
    const StateSet& ports)
{
    for (State port : ports) {
        for (auto map_pair : subset_map) {
            if (!haskey(map_pair.first, port)) {
                in_map[port].insert(map_pair.second);
            }
        }
    }
}

void complement_reverse_scc(
    Nfa*            result,
    InMap&          in_map,
    const Nfa&      aut,
    const Alphabet& alphabet,
    const StateSet& ports)
{

    Nfa aut_rev = revert(aut);

    for (State port_state : ports)
    {
        aut_rev.add_final(port_state);
    }

    Nfa aut_cmpl_rev;
    SubsetMap subset_map;

    complement_classical(&aut_cmpl_rev, aut_rev, alphabet, &subset_map);

    *result = revert(aut_cmpl_rev);

    result->initialstates = {};

    for (auto subset_map_pair : subset_map)
    {
        bool is_initial = true;
        for (State initstate : aut.initialstates)
        {
            if (haskey(subset_map_pair.first, initstate))
            {
                is_initial = false;
                break;
            }
        }
        if (is_initial)
        {
            result->add_initial(subset_map_pair.second);
        }
    }

    create_in_map_reverse(in_map, subset_map, ports);
};
// TODO
void update_in_map(
    InMap&                       in_map_result,
    const Nfa&                   aut,
    const std::vector<StateSet>& sccs,
    unsigned int                 scc_num,
    const StateSet&              ports,
    InMap&                       in_map,
    StateSetMap                  state_set_map){

};

void join_two_sccs_v2(
    Nfa*                         result,
    const Nfa&                   aut,
    const Alphabet&              alphabet,
    const std::vector<StateSet>& sccs,
    unsigned int                 next_scc,
    const Nfa&                   b_previos,
    InMap&                       in_map,
    StateToSccNumMap&            state_to_scc,
    StateSetMap*                 state_subset_map)
{

    bool delete_map = false;
    if (nullptr == state_subset_map)
    {
        state_subset_map = new StateSetMap();
        delete_map = true;
    }

    StateSet ports_first;
    const StateSet &set_first = sccs[next_scc];

    Nfa aut_first;
    automata_from_set(&aut_first, aut, set_first);

    for (const Trans &trans : aut)
    {
        if (state_to_scc[trans.src] < next_scc && state_to_scc[trans.tgt] == next_scc)
        {
            ports_first.insert(trans.tgt);
        }
    }

    Nfa aut_first_det;
    SubsetMap map_first;
    State last_state_num;
    determinize_scc(&aut_first_det, aut_first, ports_first, &map_first, &last_state_num);
    State sink_state = last_state_num + 1;
    auto it_inserted_pair = map_first.insert({{}, sink_state});
    if (!it_inserted_pair.second) {
        sink_state = it_inserted_pair.first->second;
    }
    make_complete_scc(&aut_first_det, alphabet, ports_first, sink_state);
    std::cout << "first_scc_size: " << aut_first_det.count_states() << std::endl;

    auto map_first_inverse = invert_map(map_first);

    std::cerr << "first part: " << std::endl;
    std::cerr << aut_first_det << std::endl;

    std::cerr << "first part mpa: " << std::endl;
    std::cerr << to_string(map_first) << std::endl;

    State cnt_state = 0;
    std::list<std::pair<const StateStateSetPair*, State>> worklist;

    State initstate;
    if (aut_first_det.initialstates.size() == 0)
    {
        initstate = sink_state;
    }
    else
    {
        initstate = *aut_first_det.initialstates.begin();
    }

    if (b_previos.initialstates.size() == 0)
    {
        StateStateSetPair pair = std::make_pair(initstate, StateSet());
        auto it_bool_pair = state_subset_map->insert({pair, cnt_state});
        result->initialstates = {cnt_state};
        worklist.push_back({&it_bool_pair.first->first, cnt_state});
        ++cnt_state;
    }
    else
    {
        for (State second_initstate : b_previos.initialstates)
        {
            StateSet initstates = {second_initstate};
            StateStateSetPair pair = std::make_pair(initstate, initstates);
            auto it_bool_pair = state_subset_map->insert({pair, cnt_state});
            result->initialstates.insert(cnt_state);
            worklist.push_back({&it_bool_pair.first->first, cnt_state});
            ++cnt_state;
        }
    }

    for (State port_state : ports_first)
    {
        State determ_port_state = map_first[{port_state}];
        StateStateSetPair pair = std::make_pair(determ_port_state, StateSet());
        if (!haskey(*state_subset_map, pair))
        {
            auto it_bool_pair = state_subset_map->insert({pair, cnt_state});
            worklist.push_back({&it_bool_pair.first->first, cnt_state});
            ++cnt_state;
        }
    }

    while (!worklist.empty())
    {
        const StateStateSetPair *state_state_set;
        State new_state;
        tie(state_state_set, new_state) = worklist.front();
        worklist.pop_front();
        assert(nullptr != state_state_set);

        // set the state final
        // all runs in second part accept and run in first doesnt
        if (is_subset(state_state_set->second, b_previos.finalstates) &&
            !aut_first_det.has_final(state_state_set->first))
        {
            result->finalstates.insert(new_state);
        }

        PostSymb post_determinized = aut_first_det[state_state_set->first];
        std::unordered_map<State, std::vector<StateSet>> post_complement;

        for (auto symb_set : post_determinized)
        {

            std::vector<StateSet> list;
            list.push_back(StateSet());
            for (State s : state_state_set->second)
            {
                StateSet next_set_complement;
                if (haskey(b_previos[s], symb_set.first))
                {
                    next_set_complement = b_previos[s].at(symb_set.first);
                    list = multiplyVector(list, &next_set_complement);
                }
                else
                {
                    list = std::vector<StateSet>();
                    break;
                }
            }

            // ports
            std::vector<StateSet> port_list;
            port_list.push_back(StateSet());

            for (State state_first : map_first_inverse[state_state_set->first])
            {
                auto post_symb = aut[state_first];
                if (!haskey(post_symb, symb_set.first))
                {
                    continue;
                }
                for (State original_state : post_symb[symb_set.first])
                {
                    if (haskey(in_map, original_state))
                    {
                        port_list = multiplyVector(port_list, &in_map[original_state]);
                    }
                }
            }

            std::vector<StateSet> complete_list;
            for (const StateSet &trans_set : list)
            {
                for (const StateSet &port_set : port_list)
                {
                    StateSet combined_set = port_set;
                    combined_set.insert(trans_set.begin(), trans_set.end());
                    complete_list.push_back(combined_set);
                }
            }

            remove_little_brothers(&complete_list);

            post_complement.insert({symb_set.first, complete_list});
        }

        for (auto x : post_determinized)
        {
            Symbol symbol = x.first;
            State state_determized = *x.second.begin();

            auto vector_complement = post_complement.at(symbol);

            for (auto set_complement : vector_complement)
            {
                auto pair = std::make_pair(state_determized, set_complement);
                auto it_bool_pair = state_subset_map->insert({pair, cnt_state});
                if (it_bool_pair.second)
                {
                    worklist.push_back({&it_bool_pair.first->first, cnt_state});
                    cnt_state++;
                }

                State post_state = it_bool_pair.first->second;
                result->add_trans(new_state, symbol, post_state);
            }
        }
    }
    std::cerr << to_string(*state_subset_map) << std::endl;

    if (delete_map)
    {
        delete state_subset_map;
    }
}

void create_scc_transitions(
    SccTransitionMap&       scc_transitions,
    std::vector<StateSet>   sccs,
    StateToSccNumMap&       state_to_scc_map,
    const Nfa&              aut)
{

    for (Trans trans : aut)
    {
        unsigned int scc_src = state_to_scc_map[trans.src];
        unsigned int scc_tgt = state_to_scc_map[trans.tgt];
        if (scc_src != scc_tgt)
        {
            scc_transitions[std::make_pair(scc_src, scc_tgt)].add_trans(trans);
        }
    }
}

void state_to_scc(
    const std::vector<StateSet>&             vector,
    std::unordered_map<State, unsigned int>& map)
{
    unsigned int component_number = 0;

    for (const auto &set : vector)
    {
        for (State state : set)
        {
            map[state] = component_number;
        }
        component_number++;
    }
}

void complement_sccs(
    Nfa*                result,
    const Nfa&          aut,
    const Alphabet&     alphabet,
    SubsetMap*          subset_map,
    const StringDict&   params = {})
{
    assert(nullptr != result);

    bool delete_subset_map = false;
    if (nullptr == subset_map)
    {
        subset_map = new SubsetMap();
        delete_subset_map = true;
    }

    std::vector<StateSet> scc_vector;
    scc_tarjan(scc_vector, aut);
    std::reverse(scc_vector.begin(), scc_vector.end());

    StateToSccNumMap state_to_scc_map;
    state_to_scc(scc_vector, state_to_scc_map);

    Nfa a_n;
    unsigned int last_set_num = scc_vector.size() - 1;
    automata_from_set(&a_n, aut, scc_vector[last_set_num]);

    std::cerr << "a_n: " << std::endl;
    std::cerr << a_n << std::endl;

    Nfa b_n;
    StateSet in_n;
    for (Trans trans : aut)
    {
        unsigned int scc_src = state_to_scc_map[trans.src];
        unsigned int scc_tgt = state_to_scc_map[trans.tgt];
        if (scc_src != scc_tgt && scc_tgt == last_set_num)
        {
            in_n.insert(trans.tgt);
        }
    }

    SubsetMap subset_map_n;
    InMap in_map_n;
    bool rev = false;

    if (haskey(params, "reverse"))
    {
        if (params.at("reverse") == "true")
        {
            rev = true;
        }
    }

    if (rev)
    {
        complement_reverse_scc(&b_n, in_map_n, a_n, alphabet, in_n);
    }
    else
    {
        complement_classical_scc(&b_n, a_n, in_n, alphabet, &subset_map_n);

        create_in_map(in_map_n, subset_map_n, in_n);
    }

    std::cout << "last_scc_size: " << b_n.count_states() << std::endl;

    StateSetMap state_state_set_map;

    join_two_sccs_v2(
        result,
        aut,
        alphabet,
        scc_vector,
        0,
        b_n,
        in_map_n,
        state_to_scc_map,
        &state_state_set_map);
}

int check_concat(const Nfa &aut, StateSet *set_a, StateSet *set_b)
{
    State initial_state;
    bool initial_state_found = false;
    for (State state : *set_a)
    {
        PostSymb post = aut[state];
        for (auto post_part : post)
        {
            for (State target_state : post_part.second)
            {
                if (set_b->find(target_state) != set_b->end())
                {
                    if (!initial_state_found)
                    {
                        initial_state_found = true;
                        initial_state = target_state;
                    }
                    else
                    {
                        if (target_state != static_cast<State>(initial_state))
                        {
                            return 2;
                        }
                    }
                }
            }
        }
    }

    if (!initial_state_found)
    {
        return 0;
    }

    return 1;
}

void join_scc_to_concat(
    std::vector<StateSet>&  work_list,
    const Nfa&              aut,
    std::vector<StateSet>*  concat_sets_pointer)
{
    if (work_list.size() < 2)
    {
        return;
    }
    std::vector<StateSet> concat_sets = *concat_sets_pointer;

    StateSet first_set = *work_list.begin();
    concat_sets.push_back(first_set);
    work_list.erase(work_list.begin());

    for (auto scc = work_list.begin(); scc != work_list.end(); scc++)
    {
        bool joined_sets = false;

        for (auto concat_set = concat_sets.begin(); concat_set != concat_sets.end(); concat_set++)
        {
            int number_of_connections = check_concat(aut, &(*concat_set), &(*scc));
            if (number_of_connections > 1)
            {
                StateSet new_scc = *scc;
                new_scc.insert(concat_set->begin(), concat_set->end());
                work_list.erase(scc--);
                concat_sets.erase(concat_set--);
                work_list.push_back(new_scc);
                joined_sets = true;
                break;
            }

            number_of_connections = check_concat(aut, &(*scc), &(*concat_set));
            if (number_of_connections > 1)
            {
                StateSet new_scc = *scc;
                new_scc.insert(concat_set->begin(), concat_set->end());
                work_list.erase(scc--);
                concat_sets.erase(concat_set--);
                work_list.push_back(new_scc);
                joined_sets = true;
                break;
            }
        }

        if (!joined_sets)
        {
            concat_sets.push_back(*scc);
            work_list.erase(scc--);
        }
    }

    *concat_sets_pointer = concat_sets;
}

bool get_concat_connection(
    StateSet*   set_a,
    StateSet*   set_b,
    const Nfa&  aut,
    State*      state_connecting)
{
    for (State state_a : *set_a)
    {
        auto post_symb = aut[state_a];
        for (auto pair : post_symb)
        {
            for (State state_b : *set_b)
            {
                if (pair.second.find(state_b) != pair.second.end())
                {
                    *state_connecting = state_b;
                    return true;
	            }
            }
        }
    }

    return false;
}

void create_sub_automata(
    const Nfa &aut,
    const Alphabet &alphabet,
    Nfa *result,
    std::vector<std::pair<StateSet, StateSet>> *component_string)
{
    assert(component_string->size() > 0);

    Nfa partial_result;

    StateSet last_component = component_string->back().second;
    for (State state_i : component_string->back().first)
    {
        partial_result.add_initial(state_i);
	}

    for (State state_from : last_component)
    {
        for (auto post_symb : aut[state_from])
        {
            for (State state_to : post_symb.second)
            {
                if (last_component.find(state_to) != last_component.end())
                {
                    partial_result.add_trans(state_from, post_symb.first, state_to);
                }
            }
        }

        if (aut.has_final(state_from))
        {
            partial_result.add_final(state_from);
        }
    }

    Nfa aut_complement;
    // complement_reverted(&aut_complement, partial_result, alphabet, nullptr);
    // //TODO uncomment
    complement_classical(&aut_complement, partial_result, alphabet, nullptr);
    StateSetMap state_set_map;
    for (auto i = component_string->rbegin(); i + 1 != component_string->rend(); i++)
    {
        Nfa part_aut = Nfa();

        for (State state_i : (i + 1)->first)
        {
            part_aut.add_initial(state_i);
        }
        for (State state_i : i->first)
        {
            part_aut.add_final(state_i);
        }

        for (State state_from : (i + 1)->second)
        {
            for (auto post_symb : aut[state_from])
            {
                for (State state_to : post_symb.second)
                {
                    if ((i + 1)->second.find(state_to) != (i + 1)->second.end() ||
                        i->first.find(state_to) != i->first.end())
                    {
                        part_aut.add_trans(state_from, post_symb.first, state_to);
                    }
                }
            }
        }

        SubsetMap subset_map;

        Nfa aut_determinized;

        State last_state_num;
        aut_determinized = determinize(part_aut, &subset_map, &last_state_num);
        State sink_state = last_state_num + 1;
        auto it_inserted_pair = subset_map.insert({{}, sink_state});
        if (!it_inserted_pair.second)
        {
            sink_state = it_inserted_pair.first->second;
        }

        make_complete(&aut_determinized, alphabet, sink_state);

        partial_result = Nfa();
        state_set_map = StateSetMap();

        complement_concat(&partial_result,
                          aut_determinized,
                          aut_complement,
                          alphabet,
                          &state_set_map);

        aut_complement = Nfa();
        remove_useless_states(&aut_complement, partial_result);

        StateSet previous_final_states;

        for (auto x : subset_map)
        {
            for (auto y : x.first)
            {
                if (aut.has_final(y))
                {
                    previous_final_states.insert(x.second);
                    break;
                }
            }
        }

        for (auto x : state_set_map)
        {
            if (previous_final_states.find(x.first.first) != previous_final_states.end())
            {
                aut_complement.finalstates.erase(x.second);
            }
        }
    }

    *result = aut_complement;
}

void create_concat_strings(
    std::vector<StateSet>&  work_list,
    const Nfa&              aut,
    const Alphabet&         alphabet,
    StateSet*               initial_set,
    std::vector<std::pair<StateSet, StateSet>> string_vector,
    std::vector<Nfa>&       auts)
{
    State connecting_state;
    StateSet final_set;
    std::vector<std::vector<StateSet>> vector;

    bool found_next = false;
    for (StateSet set : work_list)
    {
        if (set != *initial_set)
        {
            bool result = get_concat_connection(initial_set, &set, aut, &connecting_state);
            if (result)
            {
                found_next = true;
                std::vector<std::pair<StateSet, StateSet>> string_copy(string_vector);
                StateSet connecting_set;
                connecting_set.insert(connecting_state);
                string_copy.push_back(std::make_pair(connecting_set, set));
                create_concat_strings( work_list, aut, alphabet, &set, string_copy, auts);
            }
        }
    }

    if (!found_next) {

        Nfa result;
        create_sub_automata(aut, alphabet, &result, &string_vector);
        auts.push_back(result);
    }
}

void complement_concat_full(
    Nfa*                result,
    const Nfa&          aut,
    const Alphabet&     alphabet,
    SubsetMap*          subset_map,
    const StringDict&   params = {})
{ // {{{
    assert(nullptr != result);

    bool delete_subset_map = false;
    if (nullptr == subset_map)
    {
        subset_map = new SubsetMap();
        delete_subset_map = true;
    }

    std::vector<StateSet> vector;
    scc_tarjan(vector, aut);

    std::vector<StateSet> vector2;

    join_scc_to_concat(vector, aut, &vector2);

    StateSet initial_states;
    std::vector<Nfa> auts;

    StateSet *initial_set;
    for (auto set = vector2.begin(); set != vector2.end(); set++)
    {
        if (!are_disjoint(*set, aut.initialstates))
        {
            initial_set = &(*set);
            for (State state_a : *initial_set)
            {
                if (aut.has_initial(state_a))
                {
                    initial_states.insert(state_a);
                }
            }
            std::vector<std::pair<StateSet, StateSet>> string_vector;
            string_vector.push_back(std::make_pair(initial_states, *initial_set));

            create_concat_strings(vector2, aut, alphabet, initial_set, string_vector, auts);
        }
    }

    // intersection
    *result = auts.at(0);
    for (auto i = auts.begin() + 1; i != auts.end(); i++)
    {
        Nfa aut_intersection = intersection(*result, *i, nullptr);
        *result = aut_intersection;
    }

    if (delete_subset_map)
    {
		delete subset_map;
	}
} // complement_concat }}}

} // namespace

void Vata2::Nfa::complement(
	Nfa*               result,
	const Nfa&         aut,
	const Alphabet&    alphabet,
	const StringDict&  params,
	SubsetMap*         subset_map)
{
	// setting the default algorithm
	decltype(complement_classical)* algo = complement_classical;
	if (!haskey(params, "algo")) {
		throw std::runtime_error(std::to_string(__func__) +
			" requires setting the \"algo\" key in the \"params\" argument; "
			"received: " + std::to_string(params));
	}

    const std::string& str_algo = params.at("algo");
    if ("classical" == str_algo) {  /* default */ }
    else if ("reverse" == str_algo)
    {
        algo = complement_reverted;
    }
    else if ("reverse_min" == str_algo)
    {
        algo = complement_reverted_min;
    }
    else if ("concat" == str_algo) {
        algo = complement_concat_full;
    }
    else if ("choose_better" == str_algo)
    {
        algo = complement_choose_better;
    }
    else if ("sccs" == str_algo)
    {
        algo = complement_sccs;
    }
	else {
        throw std::runtime_error(std::to_string(__func__) +
			" received an unknown value of the \"algo\" key: " + str_algo);
	}

    algo(result, aut, alphabet, subset_map, params);
} // complement

void Vata2::Nfa::complement(
    Nfa*            result,
    const Nfa&      aut_1,
    const Alphabet& alphabet_1,
    const Nfa&      aut_2,
    const Alphabet& alphabet_2,
    StateSetMap*    state_set_map)
{
    assert(nullptr != result);

    bool delete_subset_map = false;
    if (nullptr == state_set_map)
    {
        state_set_map = new StateSetMap();
        delete_subset_map = true;
    }

    SubsetMap *subset_map = new SubsetMap();

    Nfa aut_determinized;

    State last_state_num;
    aut_determinized = determinize(aut_1, subset_map, &last_state_num);
    State sink_state = last_state_num + 1;
    auto it_inserted_pair = subset_map->insert({{}, sink_state});
    if (!it_inserted_pair.second)
    {
        sink_state = it_inserted_pair.first->second;
    }

    make_complete(&aut_determinized, alphabet_1, sink_state);

    Nfa aut_reverse_complement;

    complement_reverted(&aut_reverse_complement, aut_2, alphabet_2, nullptr);

    complement_concat(result,
                      aut_determinized,
                      aut_reverse_complement,
                      alphabet_1,
                      state_set_map);

    delete subset_map;

    if (delete_subset_map) {
        delete state_set_map;
    }
}
