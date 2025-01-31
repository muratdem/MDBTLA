import json
import networkx as nx

# 
# Computing path coverings of state graph.
# 

# 
# Generate TLC graph and convert to JSON.
# 
# tlc -dump dot,actionlabels states.dot -workers 10 -deadlock MDBTest && dot -Tjson states.dot > states.json
# 

G = nx.DiGraph()

f = open("states.dot")
lines = f.readlines()
for l in lines:
    line = l.strip()
    if " -> " in line:
        edge_parts = line.split(" ")
        # print(line.split(" ")[:3])
        head = edge_parts[0]
        tail = edge_parts[2]
        G.add_edge(head, tail)



# edges = graph['edges']

# for edge in edges:
#     # print(edge["_gvid"], edge["tail"], edge["head"])
#     print(edge["tail"], edge["head"])
#     G.add_edge(edge["tail"], edge["head"])



# f = open("states.json")
# graph = json.load(f)



print("Original graph:")
print(len(G.nodes()), "nodes")
print(len(G.edges()), "edges")

# Render G into PDF.
nx.drawing.nx_pydot.write_dot(G, "states_before.dot")
# nx.draw(G)

# Compute minimum spanning arborescence.
mst = nx.minimum_spanning_arborescence(G)

nx.drawing.nx_pydot.write_dot(mst, "states_after.dot")

ordered_nodes = list(nx.topological_sort(mst))
root_node = ordered_nodes[0]
print("Root node:", root_node)


min_flow = nx.min_cost_flow(mst)


print("MST:")
print(len(mst.nodes()), "nodes in MST")
print(len(mst.edges()), "edges in MST")
print("Min flow:")
# print(len(min_flow))
print("Min flow root outgoing:", min_flow[root_node])
for n in min_flow:
    # print(n)
    if root_node in min_flow[n]:
        print(min_flow[n][root_node])
    # print(root_node in min_flow[n])

# Consider the computed min flow, and now start at the root.


