import json
import networkx as nx
import random
import time
random.seed(10)

# 
# Computing path coverings of state graph.
# 


def sample_paths(Garg, num_paths, max_path_len, root_node):
    seen_nodes = set()

    for pn in range(num_paths):
        curr_node = root_node
        rand_path = []

        for i in range(max_path_len):
            seen_nodes.add(curr_node)
            succs = list(Garg.successors(curr_node))
            if len(succs) == 0:
                break
            # print(succs)
            new_succs = [s for s in succs if s not in seen_nodes]
            if len(new_succs) > 0:
                succs = new_succs + [random.choice(succs)]
            curr_node = random.choice(succs)
            # print(curr_node)
            rand_path.append(curr_node)
    print("Total seen nodes:",len(seen_nodes))
    print("Original nodes:", len(Garg.nodes()))

# 
# Generate TLC graph and convert to JSON.
# 
# tlc -dump dot,actionlabels states.dot -workers 10 -deadlock MDBTest && dot -Tjson states.dot > states.json
# 

# Parse TLC DOT graph manually since it's a simple format.
# f = open("states.dot")
# lines = f.readlines()
# for l in lines:
#     line = l.strip()
#     if " -> " in line:
#         edge_parts = line.split(" ")
#         # print(line.split(" ")[:3])
#         head = edge_parts[0]
#         tail = edge_parts[2]
#         G.add_edge(head, tail)

def parse_json_state_graph(fpath="states.json"):
    G = nx.DiGraph()

    # Stores mapping from graph edges to the action + parameters associated with
    # that transition edge.
    edge_actions = {}

    fgraph = open(fpath)
    json_graph = json.load(fgraph)
    for edge in json_graph["edges"]:
        G.add_edge(edge["from"], edge["to"])
        edge_actions[(edge["from"], edge["to"])] = edge

    node_map = {}
    for node in json_graph["states"]:
        node_map[node["fp"]] = node["val"]

    # print(edge_actions)
    print("Original graph:")
    print(len(G.nodes()), "nodes")
    print(len(G.edges()), "edges")

    return (G, node_map, edge_actions)

def compute_path_coverings(G, target_nodes_to_cover, cvg_pct=1.0):
    #### Compute path covering with some simple heuristics for test-case generation.

    # Compute minimum spanning arborescence (converts original graph to DAG).
    print("Computing MST arborescence...")
    start_time = time.time()
    mst = nx.minimum_spanning_arborescence(G)

    print(f"Computed MST in {time.time() - start_time:.2f} seconds.")
    print(len(mst.edges()), f"edges in MST ({100 * len(mst.edges()) / len(G.edges()):.1f}% of original)")

    ordered_nodes = list(nx.topological_sort(mst))
    root_node = ordered_nodes[0]
    print("Root node:", root_node)

    # Try a simple path covering approach by enumerating shortest paths from root, and 
    # greedily adding paths from this set until all nodes are covered (prefer longer paths first).
    spaths = nx.single_source_shortest_path(mst, root_node)
    print("shortest paths from root:", len(spaths))
    spath_keys_sorted = sorted(spaths.keys(), key=lambda x: (len(spaths[x]), hash(tuple(spaths[x]))), reverse=True)
    
    #
    # Select paths from G to cover the specified target graph nodes.
    #

    all_covered_nodes = set()
    covering_paths = []
    uncovered_target_nodes = set(target_nodes_to_cover)
    for p in spath_keys_sorted:
        # print(p, spaths[p])

        # If this path does not cover any new nodes, don't add it.
        new_covered_target_nodes = uncovered_target_nodes.intersection(spaths[p])
        if len(new_covered_target_nodes) == 0:
            continue

        # Otherwise, add it as a new covering path, and update the set of target nodes it covers.
        all_covered_nodes.update(new_covered_target_nodes)
        
        # Compute percentage of target nodes covered.
        uncovered_target_nodes = target_nodes_to_cover.difference(all_covered_nodes)
        num_target_nodes_covered = len(target_nodes_to_cover) - len(uncovered_target_nodes)

        pct_target_covered = num_target_nodes_covered / len(target_nodes_to_cover)
        
        # covering_paths.append((spaths[p], pct_target_covered))
        covering_paths.append(spaths[p])


        # if len(all_covered_nodes) >= (cvg_pct * len(mst.nodes())):
        if num_target_nodes_covered >= (cvg_pct * len(target_nodes_to_cover)):
            break

    # assert len(all_covered_nodes) >= (cvg_pct * len(mst.nodes()))
    print("Covered nodes:", len(all_covered_nodes))
    print("Path coverings:", len(covering_paths))

    # # 
    # # TODO: More efficient path covering via min-flow?
    # # https://ieeexplore.ieee.org/abstract/document/1702662
    # # 
    # min_flow = nx.min_cost_flow(mst)

    # print("Min flow:")
    # # print(len(min_flow))
    # print("Min flow root outgoing:", min_flow[root_node])
    # for n in min_flow:
    #     # print(n)
    #     if root_node in min_flow[n]:
    #         print(min_flow[n][root_node])
    #     # print(root_node in min_flow[n])


    return covering_paths

# nx.drawing.nx_pydot.write_dot(G, "states_before.dot")


# edges = graph['edges']
# for edge in edges:
#     # print(edge["_gvid"], edge["tail"], edge["head"])
#     print(edge["tail"], edge["head"])
#     G.add_edge(edge["tail"], edge["head"])

# f = open("states.json")
# graph = json.load(f)




# print("Sampling paths...")
# sample_paths(mst, 15000, 100, root_node)