#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import sys
import csv
import json
import copy
import pandas as pd
from typing import Dict
from enum import Enum
import yaml

class StateMachineType(Enum):
    StateType = 1
    MessageType = 2
    LengthType = 3
    UnknownType = 99

class StateMachine:
    name:str
    state_list: Dict[str,'StateValue']

    def __init__(self, name:str) -> None:
        self.name = name
        self.state_list: Dict[str, StateValue] = {}
        self.state_type = StateMachineType.UnknownType

        self.same_transition_list = {} 
        self.other_transition_list = {} 

        self.total_code_of_line = 0 
        self.total_global_access_num = 0 
        self.total_global_assign_num = 0 
        self.global_access_list = []
        self.global_assign_list = []
        self.median_code_of_line = 0 
        self.median_global_access_num = 0 
        self.median_global_assign_num = 0 
        self.mode_code_of_line = 0 
        self.mode_global_access_num = 0 
        self.mode_global_assign_num = 0 

        self.special_flag = 0
        self.texted_flag = 0
        self.flag_list = []

        self.tmp_val_name_list = []


    def append_state(self, state:'StateValue'):
        if str(state) not in self.state_list.keys():
            self.state_list[str(state)] = state

    def append_transition(self, transition:'StateTransition'):
        if transition.is_in_same_state():
            if str(transition) not in self.same_transition_list.keys():
                self.same_transition_list[str(transition)] = transition
        else:
            if str(transition) not in self.other_transition_list.keys():
                self.other_transition_list[str(transition)] = transition

    def get_infect_state_machines(self) -> list:
        ret = []
        for transition in self.other_transition_list.values():
            if transition.next.statev.name not in ret:
                ret.append(transition.next.statev.name)

        return ret
    
    def get_depend(self)-> list:
        ret = []
        for state_name in self.state_list.keys():
            state = self.state_list[state_name]
            if state.is_constant():
                continue
            for val in state.get_val_list():
                if val['SubClass'] != 'Constant':
                    if val not in ret:
                        ret.append(val)

        return ret
    
    def is_state_type_by_name(self)->bool:
        rname = self.name.split('::')[-1]
        if 'state' in rname.lower():
            return True
        elif 'status' in rname.lower():
            return True
        elif 'flag' in rname.lower():
            return True
        elif 'result' in rname.lower():
            return True
        return False
    
    def is_state_type_by_struct(self)->bool:
        
        if len(self.state_list) == 0:
            return False

        for statev in self.state_list.values():
            if not statev.is_constant() and not statev.is_only_bit_op():
                return False
            
        other_constant_count = 0
        for statev in self.state_list.values():
            if statev.is_constant():
                if int(float(statev.get_constant_value())) != 0 and int(float(statev.get_constant_value())) != 1 and int(float(statev.get_constant_value())) != -1 and int(float(statev.get_constant_value())) != 65535 and int(float(statev.get_constant_value())) != 65534:
                    other_constant_count = other_constant_count + 1

        if other_constant_count == 0:
            return False

        state_tran_rate = len(self.same_transition_list) / float(len(self.state_list))

        if state_tran_rate < 0.5:
            return False
        
        for statev in self.state_list.values():
            if 'new' in statev.get_expr_str():
                return False

        return True
    
    def is_message_type_by_name(self)->bool:
        rname = self.name.split('::')[-1]
        if 'type' in rname.lower():
            return True
        elif 'kind' in rname.lower():
            return True
        elif 'command' in rname.lower():
            return True
        elif 'version' in rname.lower():
            return True
        elif 'priority' in rname.lower():
            return True
        return False
        
    def is_message_type_by_struct(self)->bool:
        if len(self.state_list) == 0:
            return False

        constant_count = 0
        for statev in self.state_list.values():
            if statev.is_constant():
                constant_count = constant_count + 1

        constant_rate = constant_count / float(len(self.state_list))
        if constant_rate < 0.7:
            return False
        
        other_constant_count = 0
        for statev in self.state_list.values():
            if statev.is_constant():
                if int(float(statev.get_constant_value())) != 0 and int(float(statev.get_constant_value())) != 1 and int(float(statev.get_constant_value())) != -1 and int(float(statev.get_constant_value())) != 65535 and int(float(statev.get_constant_value())) != 65534:
                    other_constant_count = other_constant_count + 1
        if other_constant_count == 0:
            return False
        
        for statev in self.state_list.values():
            if 'new' in statev.get_expr_str():
                return False

        return True
    
    def is_length_type_by_name(self)->bool:
        rname = self.name.split('::')[-1]
        if 'length' in rname.lower():
            return True
        elif 'len' in rname.lower():
            return True
        elif 'count' in rname.lower():
            return True
        elif 'pos' in rname.lower():
            return True
        elif 'size' in rname.lower():
            return True
        elif 'index' in rname.lower():
            return True
        return False
    
    def is_length_type_by_struct(self)->bool:
        
        if len(self.state_list) == 0:
            return False
        
        for statev in self.state_list.values():
            if statev.may_lenth_type():
                return True
        
        return False
        



class StateValue:
    def __init__(self, op:str, statev:StateMachine, expr:dict, name='') -> None:
        self.op = op #==, !=, >, <, >=, <=, Unknown. fixme: +=, -=, *=, /=, &=, |=, ^=, %=, <<=, >>=, >>>=
        self.statev = statev 
        self.expr = expr 
        self.name = name

        self.same_next_state_list: Dict[str, StateValue] = {}
        self.other_next_state_list: Dict[str, StateValue] = {}
        self.compare_next_state_list: Dict[str, StateValue] = {}

        self.same_state_transition_list: Dict[str, StateTransition] = {}
        self.other_state_transition_list: Dict[str, StateTransition] = {}

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

        self.parser = ExprParser(expr)

    def is_constant(self) -> bool:
        return self.parser.constant
    
    def is_only_bit_op(self) -> bool:
        return self.parser.only_bit_op
    
    def get_constant_value(self) -> int:
        return self.parser.constant_value
    
    def may_lenth_type(self) -> bool:
        return self.parser.contain_len_type_expr or (self.parser.alt_op and self.parser.contain_len_type_expr)
    
    def get_expr_str(self):
        return self.parser.expr_str_with_op

    def get_expr_str_without_op(self):
        return self.parser.expr_str_without_op
    
    def get_val_list(self):
        return self.parser.val_list
    
    def add_next_state(self, next_state:'StateValue', state_transition:'StateTransition'):
        if next_state.statev.name == self.statev.name:
            if str(next_state) not in self.same_next_state_list.keys():
                self.same_next_state_list[str(next_state)] = next_state
                self.same_state_transition_list[str(state_transition)] = state_transition
        else:
            if str(next_state) not in self.other_next_state_list.keys():
                self.other_next_state_list[str(next_state)] = next_state
                self.other_state_transition_list[str(state_transition)] = state_transition


    def __str__(self) -> str:
        expr_str = self.get_expr_str()
        return self.statev.name + " : " + self.op + " " + expr_str

    def __eq__(self, __value: 'StateValue') -> bool:
        return str(self) == str(__value)


class StateTransition:
    def __init__(self, prev:StateValue, next:StateValue) -> None:
        self.prev = prev
        self.next = next

    def is_in_same_state(self):
        return self.prev.statev.name == self.next.statev.name
    
    def __str__(self) -> str:
        return str(self.prev) + "\n -> \n" + str(self.next)

    def __eq__(self, __value: object) -> bool:
        return str(self) == str(__value)




class ExprParser:
    def __init__(self, expr:dict) -> None:
        self.expr = expr
        self.val_list = []
        self.constant = False
        self.constant_value = 0 
        self.only_bit_op = True 
        self.alt_op = False 
        self.contain_len_type_expr = False 

        self._contain_op = False 

        self.expr_str_with_op = self.dispacth(expr)
        self.expr_str_without_op = self.get_expr_str_without_op()
        self.constant = self.is_constant()

        if self.constant:
            try:
                self.constant_value = str(eval(self.expr_str_with_op))
            except BaseException as e:
                print(e)
                print(self.expr)
                self.constant = 0
            
        if self._contain_op and self.only_bit_op:
            self.only_bit_op = True
            
            
    def is_bit_op(self, op:str):
        if op == '<<' or op == '>>' or op == '>>>' or op == '&' or op == '|' or op == '^':
            return True
        return False
    
    def is_alt_op(self, op:str):
        if op == '+' or op == '-' or op == '*' or op == '/' or op == '%':
            return True
        return False
    
    def is_len_type_expr(self, value:'str'):
        rvalue = value.split('::')[-1]
        if 'length' in rvalue.lower():
            return True
        elif 'len' in rvalue.lower():
            return True
        elif 'count' in rvalue.lower():
            return True
        elif 'pos' in rvalue.lower():
            return True
        elif 'size' in rvalue.lower():
            return True
        elif 'index' in rvalue.lower():
            return True
        return False

    def dispacth(self, val:dict):
        if val['Class'] == 'Val':
            return self.deal_val(val)
        elif val['Class'] == 'Op':
            return self.deal_op(val)

    def deal_val(self, val:dict):
        if self.is_len_type_expr(val['Value']):
            self.contain_len_type_expr = True

        self.val_list.append(val)

        return val['Value']

    def deal_op(self, op:dict):
        self._contain_op = True

        total = ''
        if not self.is_bit_op(op['Operator']):
            self.only_bit_op = False

        if self.is_alt_op(op['Operator']):
            self.alt_op = True

        for val in op['Value']:
            ret =  self.dispacth(val) 
            total = total + ' ' + op['Operator'] + ' ' + ret

        if len(op['Value']) == 1:
            total = '(' + total + ')'
        else:
            remove_len = len(' ' + op['Operator'])
            total = total[remove_len:]
            total = '(' + total + ')'

        return total
    
    def is_constant(self):
        for val in self.val_list:
            if val['SubClass'] != 'Constant':
                return False
        return True
    
    def get_expr_str_without_op(self):
        total = ''
        for val in self.val_list:
            total = total + val['Value'] + ', '
        
        return total



class ExprSplit:
    def __init__(self, expr:dict) -> None:
        self.whole_expr = expr
        self.split_expr_list = []
        
        self.split_expr()

    def get_split_expr_list(self):
        return self.split_expr_list

    def split_expr(self):
        self.split_expr_list.append(self.whole_expr)
        
        while True:
            to_deal_expr = None

            for expr in self.split_expr_list:
                if self.get_a_split_expr(expr) != None:
                    to_deal_expr = expr
                    break
            
            if to_deal_expr == None:
                return
            
            #print("split " + str(to_deal_expr))
            self.split_expr_list.remove(to_deal_expr)

            new_split_expr_list = self.split_a_expr(to_deal_expr)

            for new_expr in new_split_expr_list:
                #print("new extend " + str(new_expr))
                self.split_expr_list.append(new_expr)

    def split_a_expr(self, expr:dict):
        target_expr = self.get_a_split_expr(expr)
        count = len(target_expr['Value'])

        ret = []
        for replace_expr in target_expr['Value']:
            new_expr = copy.deepcopy(expr)
            new_replace_expr = copy.deepcopy(replace_expr)
            #print("replace expr: " + str(replace_expr))
            if new_expr == target_expr:
                new_expr = new_replace_expr 
            else:
                self.replace_expr(new_expr, target_expr, new_replace_expr)
            ret.append(new_expr)

        return ret


    def get_a_split_expr(self, expr:dict):
        if expr['Class'] == 'Split' or expr['Class'] == 'CallSplit':
            return expr
        
        if expr['Class'] == 'Val':
            return None
        
        if expr['Class'] == 'Op':
            for val in expr['Value']:
                ret = self.get_a_split_expr(val)
                if ret != None:
                    return ret

    def do_replace_expr(self, expr:dict, target_expr:dict, replace_expr:dict):
        if expr == target_expr:
            raise "do_replace_expr replace: " + str(expr) + " with " + str(target_expr)
        
        if expr['Class'] == 'Val':
            return
        else:
            if target_expr in expr['Value']:
                expr['Value'].replace(target_expr, replace_expr)
            else:
                for val in expr['Value']:
                    self.do_replace_expr(val, target_expr, replace_expr)

    def replace_expr(self, expr:dict, target_expr:dict, replace_expr:dict):
        if expr['Class'] == 'Val':
            raise "replace: " + str(expr) + " with " + str(target_expr)
        else:
            if val in expr['Value']:
                expr['Value'].replace(target_expr, replace_expr)
            else:
                for val in expr['Value']:
                    self.do_replace_expr(val, target_expr, replace_expr)
            

class StateCollection:
    def __init__(self) -> None: 
        self.state_machine_list: Dict[str, StateMachine] = {}
        self.relation_list = []
        self.user_config = None
        self.state_machine_user_config = None
        self.state_machine_val_names = {}

    def set_user_config(self, config_yml_file_path:str):
        with open(config_yml_file_path, 'r') as f:
            self.user_config = yaml.safe_load(f)

            self.state_machine_user_config = {}
            self.state_machine_user_config['special_flag'] = []
            self.state_machine_user_config['texted_flag'] = []

            self.state_machine_user_config['State'] = []
            for info in self.user_config['State']:
                self.state_machine_user_config['State'].append(info['name'])
                if info['special_flag'] == 1:
                    self.state_machine_user_config['special_flag'].append(info['name'])
                if len(info['val_name']) > 0 and info['val_name'][0] is not None:
                    self.state_machine_user_config['texted_flag'].append(info['name'])
                    self.state_machine_val_names[info['name']] = info['val_name']
            self.state_machine_user_config['Type'] = []
            for info in self.user_config['Type']:
                if info is None:
                    continue
                self.state_machine_user_config['Type'].append(info['name'])
                if info['special_flag'] == 1:
                    self.state_machine_user_config['special_flag'].append(info['name'])
                if len(info['val_name']) > 0 and info['val_name'][0] is not None:
                    self.state_machine_user_config['texted_flag'].append(info['name'])
                    self.state_machine_val_names[info['name']] = info['val_name']
            self.state_machine_user_config['Unknown'] = []
            for info in self.user_config['Unknown']:
                if info is None:
                    continue
                self.state_machine_user_config['Unknown'].append(info['name'])


    def obtain_state_machines(self,file_name:str):
        with open(file_name, 'r') as f:
            reader = csv.reader(f)
            for row in reader:
                for line in row[3].split("\n"):
                    state_name = line
                    if state_name not in self.state_machine_list.keys():
                        self.state_machine_list[state_name] = StateMachine(state_name)

    def obtain_state_machines_pd(self,file_name:str):
        df = pd.read_csv(file_name, header=None)
        for index, row in df.iterrows():
            for line in row[3].split("\n"):
                state_name = line
                if state_name not in self.state_machine_list.keys():
                    self.state_machine_list[state_name] = StateMachine(state_name)
    
    def obtain_state_relation(self, file_name:str):
        with open(file_name, 'r') as f:
            reader = csv.reader(f)
            for row in reader:
                for temp in row[3].split("\n"):
                    try:
                        content = json.loads(temp)
                    except Exception as e:
                        print(temp)
                        raise e
                    self.relation_list.append(content)
                    #print(content)

    def obtain_state_relation_pd(self, file_name:str):
        df = pd.read_csv(file_name, header=None)
        for index, row in df.iterrows():
            for temp in row[3].split("\n"):
                try:
                    content = json.loads(temp)
                except Exception as e:
                    print(temp)
                    continue
                self.relation_list.append(content)
                #print(content)

    def obtain_state_and_transitions(self):
        for data in self.relation_list:
            prev_state_name = data['StateVName']
            prev_state_op = self.get_state_assingment(data['Range'])
            prev_spliter = ExprSplit(data['Condition'])

            for expr in prev_spliter.get_split_expr_list():

                #print("deal sub pre " + str(expr))
                state_value = StateValue(prev_state_op, self.state_machine_list[prev_state_name], expr)
                self.state_machine_list[prev_state_name].append_state(state_value)

                next_state_name = data['AssignVName']
                next_state_op = '=='
                next_spliter = ExprSplit(data['Extract'])

                for extract_expr in next_spliter.get_split_expr_list():
                    #print("deal sub next " + str(extract_expr))
                    next_state_value = StateValue(next_state_op, self.state_machine_list[next_state_name], extract_expr)
                    self.state_machine_list[next_state_name].append_state(next_state_value)
                    self.deal_state_transition(state_value, next_state_value)

    def deal_state_transition(self, prev_state:StateValue, next_state:StateValue):
        state_transition = StateTransition(prev_state, next_state)
        prev_state.add_next_state(next_state, state_transition)

        self.state_machine_list[prev_state.statev.name].append_transition(state_transition)
                    

    def get_state_assingment(self, range:dict):
        if range['Type'] == 'switch':
            return '=='
        elif range['Type'] == 'if-true':
            return range['Op']
        elif range['Type'] == 'if-false':
            if range['Op'] == '==':
                return '!='
            if range['Op'] == '>':
                return '<='
            if range['Op'] == '<':
                return '>='
            if range['Op'] == '>=':
                return '<'
            if range['Op'] == '<=':
                return '>'
            if range['Op'] == '!=':
                return '=='
            #print(range)
            return 'unknwon'
        else:
            #print(range)
            return 'unknwon'
        
    def judge_state_machine_type(self, name):

        if self.user_config != None:
            nname = name.replace("/", "_")
            if nname in self.state_machine_user_config['State']:
                print('State ' + name)
                return StateMachineType.StateType
            elif nname in self.state_machine_user_config['Type']:
                print('Type ' + name)
                return StateMachineType.MessageType
            elif nname in self.state_machine_user_config['Unknown']:
                print('Unknown ' + name)
                return StateMachineType.UnknownType
            else:
                pass
                

        state_machine = self.state_machine_list[name]
        if state_machine.is_state_type_by_name():
            return StateMachineType.StateType
        elif state_machine.is_message_type_by_name():
            return StateMachineType.MessageType
        elif state_machine.is_length_type_by_name():
            return StateMachineType.LengthType
        else:
            if state_machine.is_state_type_by_struct():
                return StateMachineType.StateType
            elif state_machine.is_message_type_by_struct():
                return StateMachineType.MessageType
            elif state_machine.is_length_type_by_struct():
                return StateMachineType.LengthType
            else:
                return StateMachineType.UnknownType
            
    def judge_state_machine_type_by_name(self, name):
        state_machine = self.state_machine_list[name]
        if state_machine.is_state_type_by_name():
            return StateMachineType.StateType
        elif state_machine.is_message_type_by_name():
            return StateMachineType.MessageType
        elif state_machine.is_length_type_by_name():
            return StateMachineType.LengthType
        else:
            return StateMachineType.UnknownType
            
    def judge_all_state_machine_type(self):
        for name in self.state_machine_list.keys():
            state_machine = self.state_machine_list[name]
            state_machine.state_type = self.judge_state_machine_type(name)
            nname = name.replace("/", "_")
            if self.user_config != None:
                if nname in self.state_machine_user_config['special_flag']:
                    state_machine.special_flag = 1
                if nname in self.state_machine_user_config['texted_flag']:
                    state_machine.texted_flag = 1
                    if self.state_machine_val_names[nname][0] is not None:
                        state_machine.tmp_val_name_list = self.state_machine_val_names[nname]

    def judge_all_state_machine_type_by_name(self):
        for name in self.state_machine_list.keys():
            state_machine = self.state_machine_list[name]
            state_machine.state_type = self.judge_state_machine_type_by_name(name)
        

if __name__ == "__main__":
    state_collection = StateCollection()
    state_collection.obtain_state_machines_pd(sys.argv[1])
    state_collection.obtain_state_relation_pd(sys.argv[2])
    state_collection.obtain_state_and_transitions()

    for state_name in state_collection.state_machine_list.keys():
        state_machine = state_collection.state_machine_list[state_name]
        for state in state_machine.state_list.keys():
            state_value = state_machine.state_list[state]
            print(state_value.expr)
            print(state_value.get_expr_str())
            print(state_value.get_expr_str_without_op())
            print(state_value.get_val_list())
            print('================================')
    #print(state_collection.state_list.__len__())
    #print(state_collection.relation_list.__len__())