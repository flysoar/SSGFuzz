from state_feedback_instrumnet import *
from state_relation_analyze import *
import shutil
import yaml
import time

class StateStaticAnalyzer:
    def __init__(self, result_name, database_path, instrument_other=False):
        self.result_name = result_name
        self.database_path = database_path
        self.instrument_other = instrument_other

        self.check_file_path()
        self.get_orgin_path()

    def check_file_path(self):
        if not os.path.exists(self.database_path):
            raise Exception("Database path not exist")
        
        self.mid_result_path = "./codeql_mid_result"
        if not os.path.exists(self.mid_result_path):
            os.mkdir(self.mid_result_path)
        
        self.result_path = "./analyze_result"
        if not os.path.exists(self.result_path):
            os.mkdir(self.result_path)

        self.result_path_name = os.path.join(self.result_path, self.result_name + '.json')

        self.state_statev_codeql_path = os.path.join(self.mid_result_path, "%s_state_statev.csv" % self.result_name)
        self.state_instrument_codeql_path = os.path.join(self.mid_result_path, "%s_instrument_codeql_result.csv" % self.result_name)
        self.state_relation_codeql_path = os.path.join(self.mid_result_path, "%s_relation_codeql_result.csv" % self.result_name)
        self.state_col_codeql_path = os.path.join(self.mid_result_path, "%s_col_codeql_result.csv" % self.result_name)
        self.state_ga_codeql_path = os.path.join(self.mid_result_path, "%s_ga_codeql_result.csv" % self.result_name)
        self.state_gc_codeql_path = os.path.join(self.mid_result_path, "%s_gc_codeql_result.csv" % self.result_name)
        self.state_comapre_codeql_path = os.path.join(self.mid_result_path, "%s_compare_codeql_result.csv" % self.result_name)

    def get_orgin_path(self):
        config_file_path = os.path.join(self.database_path, "codeql-database.yml")
        with open(config_file_path, 'r') as f:
            config = yaml.load(f, Loader=yaml.SafeLoader)
            self.origin_path = config["sourceLocationPrefix"].strip()
            

    def do_run_codeql(self, codeql_file, result_file):
        cmd = "codeql database analyze %s %s --format=csv --output %s " % (self.database_path, codeql_file, result_file)
        os.system(cmd)

    def run_codeql_analyze(self):
        self.do_run_codeql("./find_statev.ql", self.state_statev_codeql_path)
        self.do_run_codeql("./find_statev_inst.ql", self.state_instrument_codeql_path)
        self.do_run_codeql("./find_statev_relation.ql", self.state_relation_codeql_path)
        self.do_run_codeql("./find_statev_metric_mi.ql", self.state_col_codeql_path)
        self.do_run_codeql("./find_statev_metric_ga.ql", self.state_ga_codeql_path)
        self.do_run_codeql("./find_statev_metric_gc.ql", self.state_gc_codeql_path)
        self.do_run_codeql("./find_state_compare_relation.ql", self.state_comapre_codeql_path)

    def run_codeql_analyze_without_relation_obtain(self):
        self.do_run_codeql("./find_statev.ql", self.state_statev_codeql_path)
        self.do_run_codeql("./find_statev_inst.ql", self.state_instrument_codeql_path)
        self.do_run_codeql("./find_statev_metric_mi.ql", self.state_col_codeql_path)
        self.do_run_codeql("./find_statev_metric_ga.ql", self.state_ga_codeql_path)
        self.do_run_codeql("./find_statev_metric_gc.ql", self.state_gc_codeql_path)
        self.do_run_codeql("./find_state_compare_relation.ql", self.state_comapre_codeql_path)

    def do_static_analyz(self):
        self.run_codeql_analyze()

        self.state_collection = StateCollection()

        if os.path.exists(os.path.join("statev_conf", "%s.yml" % self.result_name)):
            self.state_collection.set_user_config(os.path.join("statev_conf", "%s.yml" % self.result_name))

        self.state_collection.obtain_state_machines_pd(self.state_statev_codeql_path)
        self.state_collection.obtain_state_relation_pd(self.state_relation_codeql_path)
        self.state_collection.obtain_state_and_transitions()
        self.state_collection.judge_all_state_machine_type()

        state_metric_collector = StateMetricCollection(self.state_collection)
        state_metric_collector.collect_state_col(self.state_col_codeql_path)
        state_metric_collector.collect_state_global_access(self.state_gc_codeql_path)
        state_metric_collector.collect_state_global_assign(self.state_ga_codeql_path)
        state_metric_collector.collect_state_compare_relation(self.state_comapre_codeql_path)
        state_metric_collector.collect_state_val_name_info()

        state_metric_collector.calc_state_val_metric()

        state_infomation_generation = StateInfomationGeneration(self.state_collection)
        state_infomation_generation.generate_info_list()

        if self.instrument_other:
            state_infomation_generation.generate_other_state_machine_info()

        state_inrustment = StateInrustment(state_infomation_generation)
        state_inrustment.read_codeql_result(self.state_instrument_codeql_path)
        #state_inrustment.print_codeql_result()

        state_infomation_generation.generate_json(self.result_path_name)

        return state_inrustment

    def is_all_state_machine_unknown_type(self):
        for state_machine in self.state_collection.state_machine_list.values():
            if state_machine.state_type != StateMachineType.UnknownType:
                return False
            
        return True

    def do_static_analyz_without_relation_obtain(self):
        #self.run_codeql_analyze_without_relation_obtain()

        self.state_collection = StateCollection()

        if os.path.exists(os.path.join("statev_conf", "%s.yml" % self.result_name)):
            self.state_collection.set_user_config(os.path.join("statev_conf", "%s.yml" % self.result_name))

        self.state_collection.obtain_state_machines_pd(self.state_statev_codeql_path)

        self.state_collection.judge_all_state_machine_type()

        state_metric_collector = StateMetricCollection(self.state_collection)
        state_metric_collector.collect_state_col(self.state_col_codeql_path)
        state_metric_collector.collect_state_global_access(self.state_gc_codeql_path)
        state_metric_collector.collect_state_global_assign(self.state_ga_codeql_path)
        state_metric_collector.collect_state_compare_relation(self.state_comapre_codeql_path)
        state_metric_collector.collect_state_val_name_info()

        state_metric_collector.calc_state_val_metric()

        if self.is_all_state_machine_unknown_type():
            self.state_collection.judge_all_state_machine_type()

        state_infomation_generation = StateInfomationGeneration(self.state_collection)
        state_infomation_generation.generate_info_list(True)

        if self.instrument_other:
            state_infomation_generation.generate_other_state_machine_info()

        state_inrustment = StateInrustment(state_infomation_generation)
        state_inrustment.read_codeql_result(self.state_instrument_codeql_path)
        #state_inrustment.print_codeql_result()

        state_infomation_generation.generate_json(self.result_path_name)

        return state_inrustment


    def draw_codeql_result_graph(self):
        self.graph_dir = os.path.join(self.result_path, "%s_graph" % self.result_name)
        if os.path.exists(self.graph_dir):
            shutil.rmtree(self.graph_dir)
        os.mkdir(self.graph_dir)

        state_analyzer = StateAnalyzer(self.state_collection)
        state_analyzer.build_state_machine_graphs()
        state_analyzer.draw_all_state_machine_graph(self.graph_dir)
        state_analyzer.build_overall_state_machine_graph()
        state_analyzer.draw_overall_state_machine_graph(self.graph_dir)
        state_analyzer.build_state_machine_relation_graph()
        state_analyzer.draw_state_machine_relation_graph(self.graph_dir+ '/relation')
        state_analyzer.build_state_machine_rely_graph()
        state_analyzer.draw_state_machine_rely_graph(self.graph_dir+ '/relation')


    def static_analyze_and_instrument(self):
        state_inrustment = self.do_static_analyz()
        state_inrustment.do_intrument()

    def static_analyze_and_instrument_without_relation_obtain(self):
        state_inrustment = self.do_static_analyz_without_relation_obtain()
        state_inrustment.do_intrument()

    def copy_and_bak(self):
        bak_path = self.origin_path + "_bak"

        if not os.path.exists(bak_path):
            shutil.copytree(self.origin_path, bak_path)

        if os.path.exists(self.origin_path):
            shutil.rmtree(self.origin_path)

        shutil.copytree(bak_path, self.origin_path)

    def do_static_analyze_and_instrument(self):
        self.copy_and_bak()
        self.static_analyze_and_instrument()


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("Usage: python state_static_analyze.py <result_name> <database_path> <is_instrument_other> <is_no_relation_obtain>")
        exit(0)

    # calc total time
    start_time = time.time()

    instrument_other = False

    if len(sys.argv) == 4:
        instrument_other = int(sys.argv[3])

    without_relation_obtain = False
    if len(sys.argv) == 5:
        without_relation_obtain = int(sys.argv[4])

    result_name = sys.argv[1]
    database_path = sys.argv[2]

    if without_relation_obtain:
        analyzer = StateStaticAnalyzer(result_name, database_path, instrument_other)
        analyzer.copy_and_bak()
        analyzer.static_analyze_and_instrument_without_relation_obtain()
        #analyzer.draw_codeql_result_graph()
    else:
        analyzer = StateStaticAnalyzer(result_name, database_path, instrument_other)
        analyzer.do_static_analyze_and_instrument()
        #analyzer.draw_codeql_result_graph()

    end_time = time.time()
    print("Total time: %s seconds" % (end_time - start_time))