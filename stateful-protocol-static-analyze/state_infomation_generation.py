#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from typing import Any, List
from state_metrics_deal import *
from dataclasses import dataclass, field

@dataclass(init=True, repr=True)
class StateMachineInfo:
    name = ''
    state_id = 0
    state_list: List['StateValueInfo'] = field(default_factory=list)
    state_type = StateMachineType.UnknownType.value
    code_weight = 0  # 代码行数权重
    variable_weight = 0  # 全局变量权重，或者说是对全局变量的影响的权重
    default_code_weight = 0  # 测试过程中，新发现的状态值的默认代码权重
    default_variable_weight = 0  # 测试过程中，新发现的状态值的默认全局变量权重
    special_flag = 0
    texted_flag = 0
    flag_list: List['str'] = field(default_factory=list)


@dataclass(init=True, repr=True)
class StateValueInfo:
    value = 0
    name = ''
    state_id = 0
    code_weight = 0
    variable_weight = 0
    next_statevalue: List['StateValuePair'] = field(default_factory=list)  # 可转移到的状态
    compare_relation_statevalue: List['StateValuePair'] = field(default_factory=list)  # 可转移到的状态
    metric_cc = 0
    metric_io = 0
    metric_to = 0


@dataclass(init=True, repr=True)
class StateValuePair:
    name = ''
    state_id = 0
    value = 0



class StateInfomationGeneration:
    def __init__(self, collector: StateCollection) -> None:
        self.collector = collector
        self.info_list: List[StateMachineInfo] = []
        self.global_state_id_count = 0

    def get_a_state_id(self):
        self.global_state_id_count += 1
        return self.global_state_id_count

    def is_available_state_machine(self, state_machine_name: str) -> bool:
        if state_machine_name in self.collector.state_machine_list:
            state_machine = self.collector.state_machine_list[state_machine_name]
            if state_machine.state_type == StateMachineType.StateType:
                return True
            if state_machine.state_type == StateMachineType.MessageType:
                return True
            
        return False
    
    def is_available_state_value(self, state_value: StateValue) -> bool:
        if self.is_available_state_machine(state_value.statev.name) and state_value.is_constant() and state_value.op == "==":
            return True
        return False
    
    def generate_info_list(self, is_gen_empty_state_machine: bool = False):
        for state_machine in self.collector.state_machine_list.values():
            if self.is_available_state_machine(state_machine.name):
                if len(state_machine.state_list) == 0:
                    continue
                state_machine_info = StateMachineInfo()
                state_machine_info.name = state_machine.name
                state_machine_info.state_id = self.get_a_state_id()
                state_machine_info.state_type = state_machine.state_type.value

                state_machine_info.code_weight = int(state_machine.total_code_of_line/len(state_machine.state_list))
                state_machine_info.variable_weight = int(len(state_machine.global_assign_list))


                state_machine_info.default_code_weight = int(state_machine.median_code_of_line)
                state_machine_info.default_variable_weight = int(state_machine.median_global_assign_num)

                state_machine_info.special_flag = state_machine.special_flag
                state_machine_info.texted_flag = state_machine.texted_flag
                state_machine_info.flag_list = state_machine.flag_list


                for state_value in state_machine.state_list.values():
                    if self.is_available_state_value(state_value):
                        state_value_info = StateValueInfo()
                        state_value_info.value = int(state_value.get_constant_value())
                        state_value_info.state_id = state_machine_info.state_id
                        state_value_info.name = state_value.name
                        state_value_info.metric_cc = state_value.metric_cc
                        state_value_info.metric_to = state_value.metric_to
                        state_value_info.metric_io = 0

                        for t_state in state_value.metric_io_state_list:
                            if self.is_available_state_value(t_state):
                                state_value_info.metric_io +=1



                        #使用代码行数和全局变量修改次数作为权重，代码行数为0时，使用默认权重，原因是代码行数不可能为0出现了边界情况所以置为默认值；全局变量修改次数为0时，使用1，目的是保证在调度时，发现了新路径会带来正向反馈.
                        state_value_info.code_weight = state_value.code_of_line
                        state_value_info.variable_weight = state_value.global_assign_num


                        state_machine_info.state_list.append(state_value_info)

                        for next_state in state_value.same_next_state_list.values():
                            if self.is_available_state_value(next_state):
                                state_value_pair = StateValuePair()
                                state_value_pair.name = next_state.statev.name
                                state_value_pair.value = int(float(next_state.get_constant_value()))
                                state_value_info.next_statevalue.append(state_value_pair)

                        for next_state in state_value.other_next_state_list.values():
                            if self.is_available_state_value(next_state):
                                state_value_pair = StateValuePair()
                                state_value_pair.name = next_state.statev.name
                                state_value_pair.value = int(float(next_state.get_constant_value()))
                                state_value_info.next_statevalue.append(state_value_pair)

                        for compare_relation_state in state_value.compare_next_state_list.values():
                            if self.is_available_state_value(compare_relation_state):
                                state_value_pair = StateValuePair()
                                state_value_pair.name = compare_relation_state.statev.name
                                state_value_pair.value = int(float(compare_relation_state.get_constant_value()))
                                state_value_info.compare_relation_statevalue.append(state_value_pair)

                self.info_list.append(state_machine_info)
        
        self.generate_default_state_machine_info_all(is_gen_empty_state_machine)
        self.generate_default_state_machine_info(StateMachineType.StateType)
        self.generate_default_state_machine_info(StateMachineType.MessageType)
        self.add_state_id_to_pair()

    def _get_state_id_by_name(self, name: str):
        for state_machine_info in self.info_list:
            if name == state_machine_info.name:
                return state_machine_info.state_id
            
        raise("cannot find %s state id" % name)
        return 0
    
    def get_state_id_by_name(self, name: str):
        for state_machine_info in self.info_list:
            if name == state_machine_info.name:
                return state_machine_info.state_id
            
        return 0

    def add_state_id_to_pair(self):
        for state_machine_info in self.info_list:
            for state_value_info in state_machine_info.state_list:
                for state_pair_info in state_value_info.next_statevalue:
                    state_pair_info.state_id = self._get_state_id_by_name(state_pair_info.name)
                for state_pair_info in state_value_info.compare_relation_statevalue:
                    state_pair_info.state_id = self._get_state_id_by_name(state_pair_info.name)

    def generate_default_state_machine_info_all(self, is_gen_empty_state_machine: bool = False):
        median_code_weight = 0
        median_variable_weight = 0
        median_default_code_weight = 0
        median_default_variable_weight = 0

        code_weight_list = []
        variable_weight_list = []

        default_code_weight_list = []
        default_variable_weight_list = []

        for state_machine_info in self.info_list:
            code_weight_list.append(state_machine_info.code_weight)
            variable_weight_list.append(state_machine_info.variable_weight)

            default_code_weight_list.append(state_machine_info.default_code_weight)
            default_variable_weight_list.append(state_machine_info.default_variable_weight)

        code_weight_list.sort()
        variable_weight_list.sort()
        default_code_weight_list.sort()
        default_variable_weight_list.sort()

        print("code_weight_list %s" % code_weight_list)

        if len(code_weight_list) != 0:
            self.median_code_weight = code_weight_list[int(len(code_weight_list)/2)]
        else:
            self.median_code_weight = 0

        if len(variable_weight_list) != 0:
            self.median_variable_weight = variable_weight_list[int(len(variable_weight_list)/2)]
        else:
            self.median_variable_weight = 0

        if len(default_code_weight_list) != 0:
            self.median_default_code_weight = default_code_weight_list[int(len(default_code_weight_list)/2)]
        else:
            self.median_default_code_weight = 0

        if len(default_variable_weight_list) != 0:
            self.median_default_variable_weight = default_variable_weight_list[int(len(default_variable_weight_list)/2)]
        else:
            self.median_default_variable_weight = 0

        if is_gen_empty_state_machine:
            for state_machine in self.collector.state_machine_list.values():
                print("state_machine.name %s, type %s" % (state_machine.name, state_machine.state_type.name))
                if self.is_available_state_machine(state_machine.name):
                    if len(state_machine.state_list) == 0:
                        print("state_machine.state_list is empty %s" % state_machine.name)
                        state_machine_info = StateMachineInfo()
                        state_machine_info.name = state_machine.name
                        state_machine_info.state_id = self.get_a_state_id()
                        state_machine_info.state_type = state_machine.state_type.value

                        #Now, use 10 as the default value, for log10(10) = 1, it is a good value for the default value.
                        state_machine_info.code_weight = 0
                        state_machine_info.variable_weight = 0

                        state_machine_info.default_code_weight = 0
                        state_machine_info.default_variable_weight = 0

                        state_machine_info.special_flag = state_machine.special_flag
                        state_machine_info.texted_flag = state_machine.texted_flag
                        state_machine_info.flag_list = state_machine.flag_list


    def generate_default_state_machine_info(self, state_type: StateMachineType):
        median_code_weight = 0
        median_variable_weight = 0
        median_default_code_weight = 0
        median_default_variable_weight = 0

        code_weight_list = []
        variable_weight_list = []

        default_code_weight_list = []
        default_variable_weight_list = []

        for state_machine_info in self.info_list:
            if state_machine_info.state_type == state_type.value:
                code_weight_list.append(state_machine_info.code_weight)
                variable_weight_list.append(state_machine_info.variable_weight)

                default_code_weight_list.append(state_machine_info.default_code_weight)
                default_variable_weight_list.append(state_machine_info.default_variable_weight)

        code_weight_list.sort()
        variable_weight_list.sort()
        default_code_weight_list.sort()
        default_variable_weight_list.sort()

        print("code_weight_list %s" % code_weight_list)

        if len(code_weight_list) != 0:
            median_code_weight = code_weight_list[int(len(code_weight_list)/2)]
        else:
            median_code_weight = self.median_code_weight

        if len(variable_weight_list) != 0:
            median_variable_weight = variable_weight_list[int(len(variable_weight_list)/2)]
        else:
            median_variable_weight = self.median_variable_weight
        
        if len(default_code_weight_list) != 0:
            median_default_code_weight = default_code_weight_list[int(len(default_code_weight_list)/2)]
        else:
            median_default_code_weight = self.median_default_code_weight

        if len(default_variable_weight_list) != 0:
            median_default_variable_weight = default_variable_weight_list[int(len(default_variable_weight_list)/2)]
        else:
            median_default_variable_weight = self.median_default_variable_weight

        for state_machine in self.collector.state_machine_list.values():
            if state_machine.state_type == state_type:
                if len(state_machine.state_list) == 0:
                    print("state_machine.state_list is empty %s" % state_machine.name)
                    state_machine_info = StateMachineInfo()
                    state_machine_info.name = state_machine.name
                    state_machine_info.state_type = state_machine.state_type

                    #Now, use 10 as the default value, for log10(10) = 1, it is a good value for the default value, because we don't know the real value, so we use the value that can not change the fuzz time and select time's value.
                    state_machine_info.code_weight = 0
                    state_machine_info.variable_weight = 0
                    state_machine_info.default_code_weight = 0
                    state_machine_info.default_variable_weight = 0
                    
                    state_machine_info.special_flag = state_machine.special_flag
                    state_machine_info.texted_flag = state_machine.texted_flag
                    state_machine_info.flag_list = state_machine.flag_list

    def check_alreay_exist(self, state_machine_name: str) -> bool:
        for info in self.info_list:
            if info.name == state_machine_name:
                return True
        return False

    def generate_other_state_machine_info(self):
        code_weight_list = []
        variable_weight_list = []

        default_code_weight_list = []
        default_variable_weight_list = []

        for state_machine_info in self.info_list:
            code_weight_list.append(state_machine_info.code_weight)
            variable_weight_list.append(state_machine_info.variable_weight)

            default_code_weight_list.append(state_machine_info.default_code_weight)
            default_variable_weight_list.append(state_machine_info.default_variable_weight)

        default_code_weight = 0
        default_variable_weight = 0
        code_weight = 0
        variable_weight = 0

        code_weight_list.sort()
        variable_weight_list.sort()
        default_code_weight_list.sort()
        default_variable_weight_list.sort()

        if np.average(code_weight_list) > code_weight_list[int(len(code_weight_list)/4)]:
            code_weight = code_weight_list[int(len(code_weight_list)/4)]
        else:
            code_weight = np.average(code_weight_list)
            

        if np.average(variable_weight_list) > variable_weight_list[int(len(variable_weight_list)/4)]:
            variable_weight = variable_weight_list[int(len(variable_weight_list)/4)]
        else:
            variable_weight = np.average(variable_weight_list)

        if np.average(default_code_weight_list) > default_code_weight_list[int(len(default_code_weight_list)/4)]:
            default_code_weight = default_code_weight_list[int(len(default_code_weight_list)/4)]
        else:
            default_code_weight = np.average(default_code_weight_list)

        if np.average(default_variable_weight_list) > default_variable_weight_list[int(len(default_variable_weight_list)/4)]:
            default_variable_weight = default_variable_weight_list[int(len(default_variable_weight_list)/4)]
        else:
            default_variable_weight = np.average(default_variable_weight_list)

        for state_machine in self.collector.state_machine_list.values():
            if self.check_alreay_exist(state_machine.name):
                continue

            state_machine_info = StateMachineInfo()
            state_machine_info.name = state_machine.name
            state_machine_info.state_type = state_machine.state_type.value
            state_machine_info.state_id = self.get_a_state_id()

            state_machine_info.code_weight = 0
            state_machine_info.variable_weight = 0
            state_machine_info.default_code_weight = 0
            state_machine_info.default_variable_weight = 0

            state_machine_info.special_flag = state_machine.special_flag
            state_machine_info.texted_flag = state_machine.texted_flag
            state_machine_info.flag_list = state_machine.flag_list

            self.info_list.append(state_machine_info)

        

    def generate_json(self, file_name:str):

        for state_machine_info in self.info_list:
            state_machine_info.name = state_machine_info.name.replace(" ", "_")
            state_machine_info.name = state_machine_info.name.replace("/", "_")

        def convert_to_dict(obj):
            if type(obj) in [StateMachineInfo, StateValueInfo, StateValuePair]:
                return obj.__dict__

        with open(file_name, 'w') as f:
            json.dump(self.info_list, f, indent=4, default=convert_to_dict)


if __name__ == '__main__':
    state_collection = StateCollection()
    state_collection.obtain_state_machines_pd(sys.argv[1])
    state_collection.obtain_state_relation_pd(sys.argv[2])
    state_collection.obtain_state_and_transitions()
    state_collection.judge_all_state_machine_type()

    state_metric_collector = StateMetricCollection(state_collection)
    state_metric_collector.collect_state_col(sys.argv[3])
    state_metric_collector.collect_state_global_access(sys.argv[4])
    state_metric_collector.collect_state_global_assign(sys.argv[5])

    state_infomation_generation = StateInfomationGeneration(state_collection)
    state_infomation_generation.generate_info_list()
    state_infomation_generation.generate_json(sys.argv[6])
