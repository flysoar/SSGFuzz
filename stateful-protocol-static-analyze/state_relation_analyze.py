from state_relation_deal import *
from transitions import Machine
from transitions.extensions import GraphMachine
import seaborn as sns

import os


class Model:
    def __init__(self) -> None:
        return
    

class StateAnalyzer:
    def __init__(self, colletor:StateCollection):
        self.collectpr = colletor
        self.state_machine_list = colletor.state_machine_list
        self.state_machine_graphs = {}
        self.state_machine_colors = {}
        self.global_rely_lists = {}
        self.overall_state_machine_graph = None

        self.state_machine_relation_graph_m = Model()
        self.state_machine_relation_graph = None

        palette = sns.color_palette('pastel', len(self.state_machine_list.keys())).as_hex()
        for state_name in self.state_machine_list.keys():
            self.state_machine_colors[state_name] = palette.pop()

    def get_state_machine_depend(self, name):
        state_machine = self.state_machine_list[name]
        return state_machine.get_depend()
    
    def get_state_machine_depend_statev(self, name):
        state_machine = self.state_machine_list[name]
        depend_list = state_machine.get_depend()

        ret = []
        for val in depend_list:
            if val['Value'] in self.state_machine_list.keys():
                if val['Value'] not in ret:
                    ret.append(val['Value'])
        return ret
    
    def get_state_machine_depend_other_globalv(self, name):
        state_machine = self.state_machine_list[name]
        depend_list = state_machine.get_depend()

        ret = []
        if depend_list == None:
            return ret
        
        for val in depend_list:
            if val['Value'] not in self.state_machine_list.keys():
                if val['SubClass'] == 'Global' or val['SubClass'] == 'Member':
                    if val['Value'] not in ret:
                        ret.append(val['Value'])

        return ret
    
    def get_state_machine_depend_localv(self, name):
        state_machine = self.state_machine_list[name]
        depend_list = state_machine.get_depend()

        ret = []
        for val in depend_list:
            if val['Value'] not in self.state_machine_list.keys():
                if val['SubClass'] == 'Local' or val['SubClass'] == 'Parameter':
                    if val['Value'] not in ret:
                        ret.append(val['Value'])

        return ret
    
    def get_state_machine_depend_functioncall(self, name):
        state_machine = self.state_machine_list[name]
        depend_list = state_machine.get_depend()

        ret = []
        for val in depend_list:
            if val['Value'] not in self.state_machine_list.keys():
                if val['SubClass'] == 'FunctionCall':
                    if val['Value'] not in ret:
                        ret.append(val['Value'])

        return ret
    
    def get_state_machine_infected_state(self, name):
        ret = []
        for state_machine_name in self.state_machine_list.keys():
            if name == state_machine_name:
                continue
            state_machine = self.state_machine_list[state_machine_name]
            if name in state_machine.get_infect_state_machines():
                ret.append(state_machine_name)

        return ret
    
    def build_state_machine_graphs(self):
        for state_machine_name in self.state_machine_list.keys():
            state_machine = self.state_machine_list[state_machine_name]
            self.state_machine_graphs[state_machine_name] = self.build_state_machine_graph(state_machine)
            
    def build_state_machine_graph(self, state_machine:StateMachine) -> Machine:
        state_list = []
        
        for state in state_machine.state_list.keys():
            state_list.append(state)

        machine = GraphMachine(model=state_machine, states=state_list, initial='init')
        machine.style_attributes['node'][self.state_machine_colors[state_machine.name]] = {'fillcolor': self.state_machine_colors[state_machine.name]}


        for trans in state_machine.same_transition_list.values():
            prev = str(trans.prev)
            next = str(trans.next)
            machine.add_transition(trigger='', source=prev, dest=next)

        for state in state_list:
            machine.model_graphs[id(state_machine)].set_node_style(state, self.state_machine_colors[state_machine.name])

    def draw_state_machine_graph(self, name, dir):
        path = dir
        if self.judge_state_machine_type(name) == StateMachineType.StateType: 
            path = os.path.join(dir, 'State')
        elif self.judge_state_machine_type(name) == StateMachineType.MessageType:
            path = os.path.join(dir, 'Type')
        elif self.judge_state_machine_type(name) == StateMachineType.LengthType:
            path = os.path.join(dir, 'Length')
        else:
            path = os.path.join(dir, 'Unknown')

        path = os.path.join(path, name + '.png')
        path = os.path.normpath(path)
        path = path.replace('(unnamed class/struct/union)', '(unnamed class_struct_union)')
        state_machine = self.state_machine_list[name]
        state_machine.get_graph().draw(path, prog='dot')

    def draw_all_state_machine_graph(self, dir):
        if not os.path.exists(dir):
            os.makedirs(dir)

        for type_name in ['State', 'Type', 'Length', 'Unknown']:
            if not os.path.exists(os.path.join(dir, type_name)):
                os.makedirs(os.path.join(dir, type_name))

        for name in self.state_machine_list.keys():
            self.draw_state_machine_graph(name, dir)

    def build_overall_state_machine_graph(self):
        overall_state = []
        for name in self.state_machine_list.keys():
            overall_state.extend(self.state_machine_list[name].state_list.keys())

        self.overall_state_machine_graph = GraphMachine(model=self, states=overall_state, initial='init', show_state_attributes=True)

 
        for state_machine in self.state_machine_list.values():
            for trans in state_machine.same_transition_list.values():
                prev = str(trans.prev)
                next = str(trans.next)
                self.overall_state_machine_graph.add_transition('', prev, next)

            for trans in state_machine.other_transition_list.values():
                prev = str(trans.prev)
                next = str(trans.next)
                self.overall_state_machine_graph.add_transition('', prev, next)

        for state_machine_name in self.state_machine_list.keys():
            self.overall_state_machine_graph.style_attributes['node'][self.state_machine_colors[state_machine_name]] = {'fillcolor': self.state_machine_colors[state_machine_name]}
            state_machine = self.state_machine_list[state_machine_name]
            for state in state_machine.state_list.keys():
                self.overall_state_machine_graph.model_graphs[id(self)].set_node_style(state, self.state_machine_colors[state_machine_name])

    def draw_overall_state_machine_graph(self, dir):
        if not os.path.exists(dir):
            os.makedirs(dir)
        path = os.path.join(dir, 'all' + '.png')
        self.get_graph().draw(path, prog='dot')

    def build_state_machine_relation_graph(self):
        state_names = list(self.state_machine_list.keys())

        self.state_machine_relation_graph = GraphMachine(model=self.state_machine_relation_graph_m, states=state_names, initial='_', show_state_attributes=True)

        for state_machine_name in state_names:
            for target_state_name in self.state_machine_list[state_machine_name].get_infect_state_machines():
                self.state_machine_relation_graph.add_transition('', state_machine_name, target_state_name)

        for state_machine_name in state_names:
            self.state_machine_relation_graph.style_attributes['node'][self.state_machine_colors[state_machine_name]] = {'fillcolor': self.state_machine_colors[state_machine_name]}
            self.state_machine_relation_graph.model_graphs[id(self.state_machine_relation_graph_m)].set_node_style(state_machine_name, self.state_machine_colors[state_machine_name])

    def draw_state_machine_relation_graph(self, dir):
        if not os.path.exists(dir):
            os.makedirs(dir)
        path = os.path.join(dir, 'relation' + '.png')
        self.state_machine_relation_graph.get_graph().draw(path, prog='dot')

    def build_state_machine_rely_graph(self):        
        val_lsit = []
        for state_machine_name in self.state_machine_list.keys():
            temp_val_list = self.get_state_machine_depend_other_globalv(state_machine_name)
            for val in temp_val_list:
                if val not in val_lsit: 
                    val_lsit.append(val)

        for val in val_lsit:
            state_machine_names = []
            for state_machine_name in self.state_machine_list.keys():
                if val in self.get_state_machine_depend_other_globalv(state_machine_name):
                    state_machine_names.append(state_machine_name)

            self.global_rely_lists[val] = state_machine_names



    def draw_state_machine_rely_graph(self, dir):
        if not os.path.exists(dir):
            os.makedirs(dir)
        path = os.path.join(dir, 'rely' + '.png')
                
        for val in self.global_rely_lists.keys():
            state_machine_names = self.global_rely_lists[val]
            m = Model()
            machine = GraphMachine(model=m, states=state_machine_names, initial=val, show_state_attributes=True)
            for state_machine_name in state_machine_names:
                machine.style_attributes['node'][self.state_machine_colors[state_machine_name]] = {'fillcolor': self.state_machine_colors[state_machine_name]}
                machine.model_graphs[id(m)].set_node_style(state_machine_name, self.state_machine_colors[state_machine_name])

            m.get_graph().draw(path.replace('.png', '_' + val + '.png').replace('(unnamed class/struct/union)', '(unnamed class_struct_union)'), prog='dot')
            
    def judge_state_machine_type(self, name):
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


if __name__ == '__main__':
    state_collection = StateCollection()
    state_collection.obtain_state_machines_pd(sys.argv[1])
    state_collection.obtain_state_relation_pd(sys.argv[2])
    state_collection.obtain_state_and_transitions()

    state_analyzer = StateAnalyzer(state_collection)
    state_analyzer.build_state_machine_graphs()
    state_analyzer.draw_all_state_machine_graph(sys.argv[3])
    state_analyzer.build_overall_state_machine_graph()
    state_analyzer.draw_overall_state_machine_graph(sys.argv[3])
    state_analyzer.build_state_machine_relation_graph()
    state_analyzer.draw_state_machine_relation_graph(sys.argv[3]+ '/relation')
    state_analyzer.build_state_machine_rely_graph()
    state_analyzer.draw_state_machine_rely_graph(sys.argv[3]+ '/relation')


                    