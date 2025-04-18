import pandas as pd
import sys
import json
import os
from typing import List, Tuple, Dict, Set
import random

class state_machine:
    def __init__(self, id) -> None:
        self.id = id
        self.states:Dict[int,state] = {}
        self.filte_states:Dict[int,state] = {}

    def add_state(self, value):
        if value not in self.states.keys():
            self.states[value] = state(self.id, value)

    def add_trans(self, prev, next):
        self.states[prev].add_trans(next)

    def add_other_trans(self, prev_state_id, next_state_machine_id, next_state_id):
        self.states[prev_state_id].add_other_trans((next_state_machine_id, next_state_id))
        

class state:
    def __init__(self, id, value) -> None:
        self.id = id
        self.value = value
        self.next_states: List[int] = []
        self.other_next_states: List[Tuple[int, int]] = []

        self.filte_next_states: List[int] = []
        self.filte_other_next_states: List[Tuple[int, int]] = []

        self.o_filte_next_states: List[int] = []
        self.o_filte_other_next_states: List[Tuple[int, int]] = []

    def add_trans(self, next):
        if next not in self.next_states:
            self.next_states.append(next)

    def add_other_trans(self, next):
        if next not in self.other_next_states:
            self.other_next_states.append(next)
    

class state_machine_builder:
    def __init__(self, path_name, json_name='') -> None:
        self.path_name = path_name
        self.state_machines:Dict[int, state_machine] = {}
        self.skip_state_machine:List[int] = []


        self.global_trans = set()
        self.all_trans = set()

        self.info = None

        if json_name != '':
            with open(json_name, 'r') as f:
                self.info = json.load(f)
            self.preprocess_info()
        

    def check_is_state_id(self, state_machine_id):
        if self.info == None:
            return True

        for variable in self.info:
            if variable["state_id"] == int(state_machine_id):
                if variable["state_type"] == 1:
                    return True
                else:
                    return False

        return False

    def preprocess_info(self):
        for variable in self.info:
            variable['related_state_machine_id'] = set()

        for variable in self.info:
            for value in variable['state_list']:
                for next_value in value['next_statevalue']:
                    next_state_machine_id = next_value['state_id']
                    if next_state_machine_id != variable['state_id']:
                        variable['related_state_machine_id'].add(next_state_machine_id)
                        for next_variable in self.info:
                            if next_variable['state_id'] == next_state_machine_id:
                                next_variable['related_state_machine_id'].add(variable['state_id'])

    def add_state(self, state_machine_id, value):
        if not self.check_is_state_id(state_machine_id):
            return
        if state_machine_id not in self.state_machines.keys():
            self.state_machines[state_machine_id] = state_machine(state_machine_id)

        self.state_machines[state_machine_id].add_state(value)

    def add_trans(self, state_machine_id, prev, next):
        if not self.check_is_state_id(state_machine_id):
            return
        self.state_machines[state_machine_id].add_trans(prev, next)


    def deal_state_list(self, state_list):
        statemachine_dict:Dict[int, List:[int]] = {}
        global_state_machine:Dict[int, int] = {}

        add_global_tran_flag = False
        prev_state_machine_id = 0
        prev_state = 0

        add_all_tran_flag = False
        prev_all_machine_id = 0
        prev_all = 0

        for row in state_list:
            try:
                state_machine_id = int(row.state_machine)
                state_id = int(row.state)
            except:
                print(row)
                continue

            if state_machine_id in self.skip_state_machine:
                continue

            self.add_state(int(row.state_machine), int(row.state))


            if int(row.state_machine) not in statemachine_dict.keys():
                statemachine_dict[int(row.state_machine)] = []
            statemachine_dict[int(row.state_machine)].append(int(row.state))


        for state_machine_id, state_list in statemachine_dict.items():
            if len(state_list) > 1:
                for i in range(len(state_list)-1):
                    self.add_trans(state_machine_id, state_list[i], state_list[i+1])
        
            
    def obtain(self):
        df = pd.read_csv(self.path_name, header=None, names=['state_machine', 'state'])
        state_buff = []
        for row in df.itertuples():
            if int(row.state_machine) == 0:
                if len(state_buff):
                    self.deal_state_list(state_buff)

                state_buff.clear()
                continue

            state_buff.append(row)

        if len(state_buff):
            self.deal_state_list(state_buff)


    def print_raw_count(self):
        trans_count = 0
        for state_machine_obj in self.state_machines.values():
            print(state_machine_obj.id)
            print(state_machine_obj.states.keys())
            if(state_machine_obj.id in self.skip_state_machine):
                continue
            for state_obj in state_machine_obj.states.values():
                trans_count += len(state_obj.next_states)

        print(f"trans_count: {trans_count}")

        
if __name__ == '__main__':
    if len(sys.argv) < 2:
        print(f"Usage: python {sys.argv[0]} <state_coverage_log_file> [state_info_json]")
        sys.exit(1)
    path_name = sys.argv[1]
    json_name = ''
    if len(sys.argv) == 3:
        json_name = sys.argv[2]

    state_machine_builder_obj = state_machine_builder(path_name, json_name)
    state_machine_builder_obj.obtain()
    state_machine_builder_obj.print_raw_count()