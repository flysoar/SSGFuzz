#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import sys
import json
import pandas as pd
import numpy as np

from state_relation_deal import *

class ConstantStateValue(StateValue):
    def __init__(self, op: str, statev: StateMachine, val: str, name='') -> None:
        self.op = op
        self.statev = statev
        self.value = val
        self.name = name
        self.constant = True

        self.same_next_state_list = {}
        self.other_next_state_list = {}
        self.compare_next_state_list: Dict[str, StateValue] = {}

        self.same_state_transition_list = {}
        self.other_state_transition_list = {}

        self.code_of_line = 0
        self.cycle_complexity = 0 
        self.halstead_n1 = 0
        self.halstead_n2 = 0 
        self.halstead_N1 = 0
        self.halstead_N2 = 0
        self.maintainnbility_index = 1 
        self.global_access_list = [] 
        self.global_access_num = 0
        self.global_assign_list = [] 
        self.global_assign_num = 0 

        self.metric_to = 1
        self.metric_cc = 1
        self.metric_io = 1
        self.metric_io_state_list = []

    def is_constant(self) -> bool:
        return True
    
    def is_only_bit_op(self) -> bool:
        return False
    
    def get_constant_value(self) -> int:
        return self.value
    
    def may_lenth_type(self) -> bool:
        return False
    
    def get_expr_str(self):
        return self.value

    def get_expr_str_without_op(self):
        return self.value
    
    def get_val_list(self):
        return [{"Class":"Val", "SubClass":"Constant", "Value":self.value}]
    


class StateMetricCollection:
    def __init__(self, collector:StateCollection) -> None:
        self.collector = collector

    def skip_check(self, variable_name:str) -> bool:
        if "OFString" in variable_name:
            return True
        if '[' in variable_name:
            return True

    def obtain_state_metrics(self, file_name:str):
        df = pd.read_csv(file_name)
        for index, row in df.iterrows():
            for line in row[3].split('\n'):
                if line == '':
                    continue
                try:
                    state_metric = json.loads(line)
                except Exception as e:
                    print(e)
                    print(line)
                    raise e
                yield state_metric

    def find_target_state(self, state_metric:dict) -> StateValue:
        state_machine_name = state_metric['StateVName']
        state_value = state_metric['Value']
        state_op = state_metric['Condition']

        return self.do_find_target_state(state_machine_name, state_value, state_op)
    
    def do_find_target_state(self, state_machine_name, state_value, state_op):
        state_machine = self.collector.state_machine_list[state_machine_name]

        target_state = None

        for state in state_machine.state_list.values():
            if state.is_constant() and state.get_constant_value() == state_value and state.op == state_op:
                target_state = state
                break

        if target_state is None:
            target_state = ConstantStateValue(state_op, state_machine, state_value)
            if str(target_state) not in state_machine.state_list.keys():
                state_machine.state_list[str(target_state)] = target_state
            else:
                raise Exception("State Value Conflict: %s" % str(target_state))

        return target_state


    def collect_state_col(self, file_name:str) -> None:
        for state_metric in self.obtain_state_metrics(file_name):
            target_state = self.find_target_state(state_metric)

            target_state.code_of_line += state_metric['CoL']
            target_state.cycle_complexity += state_metric['CC']
            target_state.halstead_n1 += state_metric['N1D']
            target_state.halstead_n2 += state_metric['N2D']
            target_state.halstead_N1 += state_metric['N1']
            target_state.halstead_N2 += state_metric['N2']
            target_state.statev.total_code_of_line += state_metric['CoL']

        for state_machine in self.collector.state_machine_list.values():
            num_list = []
            for state in state_machine.state_list.values():
                if state.code_of_line != 0:
                    num_list.append(state.code_of_line)

            if len(num_list) == 0:
                continue

            state_machine.median_code_of_line = np.median(num_list)
            state_machine.total_code_of_line = np.sum(num_list)
            state_machine.mode_code_of_line = np.argmax(np.bincount(num_list))



    def collect_state_global_access(self, file_name:str) -> None:
        for state_metric in self.obtain_state_metrics(file_name):
            target_state = self.find_target_state(state_metric)

            var_list = []
            for var in state_metric['GlobalAccess'].split(","):
                var = var.strip()
                if var == "":
                    continue
                if self.skip_check(var):
                    continue

                var_list.append(var)

            target_state.global_access_num += len(var_list)
            target_state.statev.total_global_access_num += len(var_list)

            for var in var_list:
                if var not in target_state.global_access_list:
                    target_state.global_access_list.append(var)
                if var not in target_state.statev.global_access_list:
                    target_state.statev.global_access_list.append(var)

        for state_machine in self.collector.state_machine_list.values():
            num_list = []
            for state in state_machine.state_list.values():
                if state.global_access_num != 0:
                    num_list.append(state.global_access_num)

            if len(num_list) == 0:
                continue

            state_machine.median_global_access_num = np.median(num_list)
            state_machine.total_global_access_num = np.sum(num_list)
            state_machine.mode_global_access_num = np.argmax(np.bincount(num_list))



    def collect_state_global_assign(self, file_name:str) -> None:
        for state_metric in self.obtain_state_metrics(file_name):
            target_state = self.find_target_state(state_metric)

            var_list = []
            for var in state_metric['GlobalAssign'].split(","):
                var = var.strip()
                if var == "":
                    continue
                if self.skip_check(var):
                    continue

                var_list.append(var)

            target_state.global_assign_num += len(var_list)
            target_state.statev.total_global_assign_num += len(var_list)

            for var in var_list:
                if var not in target_state.global_assign_list:
                    target_state.global_assign_list.append(var)
                if var not in target_state.statev.global_assign_list:
                    target_state.statev.global_assign_list.append(var)

        for state_machine in self.collector.state_machine_list.values():
            num_list = []
            for state in state_machine.state_list.values():
                if state.global_assign_num != 0:
                    num_list.append(state.global_assign_num)

            if len(num_list) == 0:
                continue

            state_machine.median_global_assign_num = np.median(num_list)
            state_machine.total_global_assign_num = np.sum(num_list)
            state_machine.mode_global_assign_num = np.argmax(np.bincount(num_list))

    def collect_state_compare_relation(self, file_name:str) -> None:
        df = pd.read_csv(file_name)
        for index, row in df.iterrows():
            for line in row[3].split('\n'):
                if line == '':
                    continue
                target_state_machine = line.split(",")[0].strip()
                target_state_value = line.split(",")[2].strip()
                next_state_machine = line.split(",")[1].strip()
                next_state_value = line.split(",")[3].strip()

                if next_state_value == 'switch':
                    continue

                target_state = self.do_find_target_state(target_state_machine, target_state_value, "==")
                next_state = self.do_find_target_state(next_state_machine, next_state_value, "==")

                if str(next_state) not in target_state.compare_next_state_list.keys():
                    target_state.compare_next_state_list[str(next_state)] = next_state

    def collect_state_val_name_info(self) -> None:
        for state_machine in self.collector.state_machine_list.values():
            print(state_machine.name)
            print(state_machine.tmp_val_name_list)
            for name_info in state_machine.tmp_val_name_list:
                val_name = name_info.split(",")[0].strip()
                val_val = name_info.split(",")[1].strip()
                if state_machine.special_flag == 1:
                    state_machine.flag_list.append(val_name)
                elif val_val == "":
                    state_machine.flag_list.append(val_name)
                else:
                    target_state = self.do_find_target_state(state_machine.name, val_val, "==")
                    target_state.name = val_name

    def calc_state_val_cc(self) -> None:
        for state_machine in self.collector.state_machine_list.values():
            for state in state_machine.state_list.values():
                state.maintainnbility_index = 171 - 5.2*np.log((state.halstead_N1+state.halstead_N2)*np.log2(state.halstead_n1+state.halstead_n2)) - 0.23*state.cycle_complexity - 16.2*np.log(state.code_of_line)
                state.metric_cc = 100 - max(0, state.maintainnbility_index*(100.0/171.0))

    def calc_state_val_io(self) -> None:
        for state_machine in self.collector.state_machine_list.values():
            for state in state_machine.state_list.values():
                for var in state.global_assign_list:
                    for t_state_machine in self.collector.state_machine_list.values():
                        for t_state in t_state_machine.state_list.values():
                            if var in t_state.global_access_list:
                                if t_state is not state:
                                    if t_state not in state.metric_io_state_list:
                                        state.metric_io_state_list.append(t_state)
                                        state.metric_io += 1

    def calc_state_val_to(self) -> None:
        for state_machine in self.collector.state_machine_list.values():
            for state in state_machine.state_list.values():
                state.metric_to = len(state.same_next_state_list) + len(state.other_next_state_list)

    def calc_state_val_metric(self) -> None:
        self.calc_state_val_cc()
        self.calc_state_val_io()
        self.calc_state_val_to()

    def print_state_metrics(self)->None:
        for state_machine in self.collector.state_machine_list.values():
            print("State Machine: %s" % state_machine.name)
            print("\tCode of Line: %d" % state_machine.total_code_of_line)
            print("\tGlobal Access: %d" % state_machine.total_global_access_num)
            print("\tGlobal Assign: %d" % state_machine.total_global_assign_num)
            print("\tGlobal Access List: " + str(state_machine.global_access_list))
            print("\tGlobal Assign List: " + str(state_machine.global_assign_list))
            print("\tMedian Code of Line: %d" % state_machine.median_code_of_line)
            print("\tMode Code of Line: %d" % state_machine.mode_code_of_line)
            print("\tMedian Global Access: %d" % state_machine.median_global_access_num)
            print("\tMode Global Access: %d" % state_machine.mode_global_access_num)
            print("\tMedian Global Assign: %d" % state_machine.median_global_assign_num)
            print("\tMode Global Assign: %d" % state_machine.mode_global_assign_num)
            print("\tState List:")

            for state in state_machine.state_list.values():
                print("\t" + str(state))
                print("\t\tCode of Line: %d" % state.code_of_line)
                print("\t\tGlobal Access: %d" % state.global_access_num)
                print("\t\tGlobal Assign: %d" % state.global_assign_num)
                print("\t\tGlobal Access List: " + str(state.global_access_list))
                print("\t\tGlobal Assign List: " + str(state.global_assign_list))



if __name__ == "__main__":
    state_collection = StateCollection()
    state_collection.obtain_state_machines_pd(sys.argv[1])
    state_collection.obtain_state_relation_pd(sys.argv[2])
    state_collection.obtain_state_and_transitions()
    state_collection.judge_all_state_machine_type()

    state_metric_collector = StateMetricCollection(state_collection)
    state_metric_collector.collect_state_col(sys.argv[3])
    state_metric_collector.collect_state_global_access(sys.argv[4])
    state_metric_collector.collect_state_global_assign(sys.argv[5])

    state_metric_collector.print_state_metrics()