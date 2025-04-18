# Define the Universal Cyclotomic Field
UCF = UniversalCyclotomicField()
E = UCF.gen

# Simplify Z2xZ2 (Klein four-group) directly using generators
from sage.groups.perm_gps.permgroup_named import KleinFourGroup
Z2xZ2 = KleinFourGroup()

# Function to convert an element of Z2xZ2 to coordinates [x_1, x_2]
def get_coordinates(element):
    # Map elements to coordinates based on their group structure
    coords_map = {
        Z2xZ2.identity(): [0, 0],
        Z2xZ2.gens()[0]: [1, 0],  # First generator
        Z2xZ2.gens()[1]: [0, 1],  # Second generator
        Z2xZ2.gens()[0] * Z2xZ2.gens()[1]: [1, 1]  # Product of generators
    }
    return coords_map[element]

# Function to calculate q(x_1, x_2) as E(4)^(a*x_1^2 + b*x_2^2 + 2*c*x_1*x_2)
def Q(coords, a, b, c):
    x1, x2 = coords
    exponent = (a * x1**2 + b * x2**2 + 2 * c * x1 * x2)
    return E(4)**exponent

# Mapping of indices to coordinates (simplified and explicit)
index_to_coords = {
    1: [0, 0], 2: [0, 0], 3: [0, 0], 4: [0, 0], 8: [0, 0],
    6: [1, 0], 10: [1, 0],
    7: [0, 1], 9: [0, 1],
    5: [1, 1], 11: [1, 1]
}

# Function to generate the required list for given parameters (a, b, c)
def generate_list(a, b, c):
    return [Q(index_to_coords[i], a, b, c) for i in range(1, 12)]

# Given list in UCF
spins = [0, 0, 0, 0, -1/16, -1/16, -1/16, -1/4, 7/16, 7/16, 7/16]
given_list = [1 if i == 0 else E(i.denominator())^i.numerator() for i in spins]

# Function to calculate the Hadamard product (component-wise) of two lists
def hadamard_product(list1, list2):
    if len(list1) != len(list2):
        raise ValueError("Lists must have the same length")
    return [x * y for x, y in zip(list1, list2)]

# Generate all possible lists
all_lists = []
for a in range(4):
    for b in range(4):
        for c in range(2):
            all_lists.append((a, b, c, generate_list(a, b, c)))

# Calculate the Hadamard product of each list with the given list
hadamard_products = []
for a, b, c, current_list in all_lists:
    product = hadamard_product(current_list, given_list)
    hadamard_products.append((a, b, c, product))
    
# Recover the spin
def recover_spin(elem):
    order = next(d for d in range(1, 16+1) if elem^d == 1)
    exponent = next(n for n in range(order) if elem == UCF.gen(order, n))
    return Integer(exponent)/Integer(order)  

# Output results
for params in hadamard_products:
    print([recover_spin(i) for i in params[3]])

# Execution
'''
sage: %attach ZestD42.sage
[0, 0, 0, 0, 15/16, 15/16, 15/16, 3/4, 7/16, 7/16, 7/16]
[0, 0, 0, 0, 7/16, 15/16, 15/16, 3/4, 7/16, 7/16, 15/16]
[0, 0, 0, 0, 3/16, 15/16, 3/16, 3/4, 11/16, 7/16, 11/16]
[0, 0, 0, 0, 11/16, 15/16, 3/16, 3/4, 11/16, 7/16, 3/16]
[0, 0, 0, 0, 7/16, 15/16, 7/16, 3/4, 15/16, 7/16, 15/16]
[0, 0, 0, 0, 15/16, 15/16, 7/16, 3/4, 15/16, 7/16, 7/16]
[0, 0, 0, 0, 11/16, 15/16, 11/16, 3/4, 3/16, 7/16, 3/16]
[0, 0, 0, 0, 3/16, 15/16, 11/16, 3/4, 3/16, 7/16, 11/16]
[0, 0, 0, 0, 3/16, 3/16, 15/16, 3/4, 7/16, 11/16, 11/16]
[0, 0, 0, 0, 11/16, 3/16, 15/16, 3/4, 7/16, 11/16, 3/16]
[0, 0, 0, 0, 7/16, 3/16, 3/16, 3/4, 11/16, 11/16, 15/16]
[0, 0, 0, 0, 15/16, 3/16, 3/16, 3/4, 11/16, 11/16, 7/16]
[0, 0, 0, 0, 11/16, 3/16, 7/16, 3/4, 15/16, 11/16, 3/16]
[0, 0, 0, 0, 3/16, 3/16, 7/16, 3/4, 15/16, 11/16, 11/16]
[0, 0, 0, 0, 15/16, 3/16, 11/16, 3/4, 3/16, 11/16, 7/16]
[0, 0, 0, 0, 7/16, 3/16, 11/16, 3/4, 3/16, 11/16, 15/16]
[0, 0, 0, 0, 7/16, 7/16, 15/16, 3/4, 7/16, 15/16, 15/16]
[0, 0, 0, 0, 15/16, 7/16, 15/16, 3/4, 7/16, 15/16, 7/16]
[0, 0, 0, 0, 11/16, 7/16, 3/16, 3/4, 11/16, 15/16, 3/16]
[0, 0, 0, 0, 3/16, 7/16, 3/16, 3/4, 11/16, 15/16, 11/16]
[0, 0, 0, 0, 15/16, 7/16, 7/16, 3/4, 15/16, 15/16, 7/16]
[0, 0, 0, 0, 7/16, 7/16, 7/16, 3/4, 15/16, 15/16, 15/16]
[0, 0, 0, 0, 3/16, 7/16, 11/16, 3/4, 3/16, 15/16, 11/16]
[0, 0, 0, 0, 11/16, 7/16, 11/16, 3/4, 3/16, 15/16, 3/16]
[0, 0, 0, 0, 11/16, 11/16, 15/16, 3/4, 7/16, 3/16, 3/16]
[0, 0, 0, 0, 3/16, 11/16, 15/16, 3/4, 7/16, 3/16, 11/16]
[0, 0, 0, 0, 15/16, 11/16, 3/16, 3/4, 11/16, 3/16, 7/16]
[0, 0, 0, 0, 7/16, 11/16, 3/16, 3/4, 11/16, 3/16, 15/16]
[0, 0, 0, 0, 3/16, 11/16, 7/16, 3/4, 15/16, 3/16, 11/16]
[0, 0, 0, 0, 11/16, 11/16, 7/16, 3/4, 15/16, 3/16, 3/16]
[0, 0, 0, 0, 7/16, 11/16, 11/16, 3/4, 3/16, 3/16, 15/16]
[0, 0, 0, 0, 15/16, 11/16, 11/16, 3/4, 3/16, 3/16, 7/16]

'''    

