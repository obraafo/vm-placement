import com.google.common.collect.Lists;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.variables.BoolVar;
import org.chocosolver.solver.variables.IntVar;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.BiFunction;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import static java.lang.String.format;
import static java.util.Arrays.asList;
import static java.util.stream.Collectors.toList;

public class PlacementSolver {

    private static final String delimiter = "-";

    SortedMap<String, Integer> regionPrefixes = new TreeMap<>();
    SortedMap<String, Integer> dcPrefixes = new TreeMap<>();
    SortedMap<String, Integer> cabinetPrefixes = new TreeMap<>();
    SortedMap<String, Integer> hypervisorPrefixes = new TreeMap<>();

    public static void main(String[] args) {
        Set<Node> inventory = createInventory(10);
        SortedMap<String, Integer> stats = new TreeMap<>();
        for (Node n : inventory) {
            String key = String.join(delimiter, n.region, n.dc, n.cabinet, n.hypervisor);
            stats.put(key, stats.getOrDefault(key, 0) + 1);
        }
        System.out.println("inventory:");
        stats.forEach((k, c) -> System.out.println(format("%1$10s:%2$3d", k, c)));

        new PlacementSolver().solve(stats);
    }

    private void solve(SortedMap<String, Integer> stats) {
        stats.forEach((k, v) -> {
            String[] parts = k.split(delimiter);
            BiFunction<String, Integer, Integer> counter = (d, c) -> c == null ? v : c + v;
            regionPrefixes.compute(String.join(delimiter, parts[0]), counter);
            dcPrefixes.compute(String.join(delimiter, parts[0], parts[1]), counter);
            cabinetPrefixes.compute(String.join(delimiter, parts[0], parts[1], parts[2]), counter);
            hypervisorPrefixes.compute(String.join(delimiter, parts[0], parts[1], parts[2], parts[3]), counter);
        });

        List<NodeRequest> req = asList(
                new NodeRequest("Americas", "dc1", "cab1", "hyp1"),
                new NodeRequest("Americas", "dc1", "cab1", "hyp1"),
                new NodeRequest("Americas", "dc1", "cab1", "hyp1"),
                new NodeRequest("Americas", "dc1", "cab1", "hyp1"),
                new NodeRequest("Americas", "dc1", "cab1", "hyp1"),
//                new NodeRequest("Americas", "dc1", "cab1", "hyp2"),
                new NodeRequest("Americas", "dc1", "cab1", "hyp2"),
//                new NodeRequest("Americas", "dc1", "cab1", "hyp1"),
//                new NodeRequest("Americas", "dc1", "cab1", "hyp2"),
//                new NodeRequest("Asia", "dc1", "cab1", "hyp3"),
//                new NodeRequest("EMEA", "dc1", "cab1", "hyp4"),
                new NodeRequest("EMEA", "dc1", "cab1", "hyp4")
        );

        Model model = new Model("placement solver");

        List<IntVar> vars = new ArrayList<>();
        List<IntVar> regionVars = new ArrayList<>();
        List<IntVar> datacenterVars = new ArrayList<>();
        List<IntVar> cabinetVars = new ArrayList<>();
        List<IntVar> hypervisorVars = new ArrayList<>();

        // variable domains
        for (int i = 0; i < req.size(); i++) {
//            System.out.println("Setting domain for node " + (i+1));
            NodeRequest r = req.get(i);

            int regionVal = regionInt(r.getRegion());
            IntVar region = model.intVar(format("%d_1_region", i), regionVal);
            vars.add(region);
            regionVars.add(region);
            model.arithm(region, "=", regionVal).post();

            int[] dcRange = dcRange(r.getRegion());
            IntVar datacenterVar = model.intVar(format("%d_2_dc", i), dcRange);
            vars.add(datacenterVar);
            datacenterVars.add(datacenterVar);

            int[] cabinetRange = cabinetRange(r.getCabinet(), dcRange);
            IntVar cabinetVar = model.intVar(format("%d_3_cab", i), cabinetRange);
            vars.add(cabinetVar);
            cabinetVars.add(cabinetVar);

            int[] hypervisorRange = hypervisorRange(r.getHypervisor(), cabinetRange);
            IntVar hypervisorVar = model.intVar(format("%d_4_hyp", i), hypervisorRange);
            vars.add(hypervisorVar);
            hypervisorVars.add(hypervisorVar);
        }

        // relative constraints
        for (int i = 0; i < req.size(); i++) {
            for (int j = i; j < req.size(); j++) {
                if (j == i) {
                    continue;
                }

                NodeRequest left = req.get(i);
                NodeRequest right = req.get(j);

                // relative constraint relations
                for (int k = 1; k < 4; k++) {
                    boolean sameRegion = left.getRegion().equals(right.getRegion());
                    boolean sameDataCenter = sameRegion && left.getDc().equals(right.getDc());
                    boolean sameCabinet = sameDataCenter && left.getCabinet().equals(right.getCabinet());
                    boolean sameHypervisor = sameCabinet && left.getHypervisor().equals(right.getHypervisor());
                    switch (k) {
                        case 1:
                            model.arithm(vars.get(i + k), sameDataCenter ? "=" : "!=", vars.get(j * 4 + k)).post();
                            break;
                        case 2:
                            model.arithm(vars.get(i + k), sameCabinet ? "=" : "!=", vars.get(j * 4 + k)).post();
                            break;
                        case 3:
                            model.arithm(vars.get(i + k), sameHypervisor ? "=" : "!=", vars.get(j * 4 + k)).post();
                    }
                }
            }
        }

        // supply constraints
        List<String> regions = new ArrayList<>(regionPrefixes.keySet());
        regionPrefixes.forEach((k,v) ->{
            String name = format("counts_%s", k);
            IntVar availability = model.intVar(name, 0, v, true);
            List<BoolVar> matchingRegion = regionVars.stream()
                    .map(rv -> model.intEqView(rv, regions.indexOf(k)))
                    .collect(toList());
            model.sum(matchingRegion.toArray(new BoolVar[]{}), "<=", availability).post();
        });

        List<String> datacenters = new ArrayList<>(dcPrefixes.keySet());
        dcPrefixes.forEach((k,v) -> {
            String name = format("counts_%s", k);
            IntVar availability = model.intVar(name, 0, v, true);
            List<BoolVar> matchingDataCenter = datacenterVars.stream()
                    .map(rv -> model.intEqView(rv, datacenters.indexOf(k)))
                    .collect(toList());
            model.sum(matchingDataCenter.toArray(new BoolVar[]{}), "<=", availability).post();
        });

        List<String> cabinets = new ArrayList<>(cabinetPrefixes.keySet());
        cabinetPrefixes.forEach((k,v) -> {
            String name = format("counts_%s", k);
            IntVar availability = model.intVar(name, 0, v, true);
            List<BoolVar> matchingDataCenter = cabinetVars.stream()
                    .map(rv -> model.intEqView(rv, cabinets.indexOf(k)))
                    .collect(toList());
            model.sum(matchingDataCenter.toArray(new BoolVar[]{}), "<=", availability).post();
        });

        List<String> hypervisors = new ArrayList<>(hypervisorPrefixes.keySet());
        hypervisorPrefixes.forEach((k,v) -> {
            IntVar availability = model.intVar(format("counts_%s", k), 0, v, true);
            List<BoolVar> matchingHypervisors = hypervisorVars.stream()
                    .map(rv -> model.intEqView(rv, hypervisors.indexOf(k)))
                    .collect(toList());
            model.sum(matchingHypervisors.toArray(new BoolVar[]{}), "<=", availability).post();
        });

        System.out.println("Problem Statement:\n" + model);
        boolean atLeastOneSolution = false;
        if (model.getSolver().solve()) {
            atLeastOneSolution = true;
            System.out.println("found a solution:");
            List<List<IntVar>> solution = Lists.partition(vars, 4);
            AtomicInteger cnt = new AtomicInteger();
            solution.forEach(s -> {
//                System.out.println(s);
                NodeRequest r = req.get(cnt.getAndIncrement());
                String region = new ArrayList<>(regionPrefixes.keySet()).get(s.get(0).getValue());
                String datacenter = new ArrayList<>(dcPrefixes.keySet()).get(s.get(1).getValue());
                String cabinet = new ArrayList<>(cabinetPrefixes.keySet()).get(s.get(2).getValue());
                String hypervisor = new ArrayList<>(hypervisorPrefixes.keySet()).get(s.get(3).getValue());
                System.out.println(new Node(r.os, r.shape, region, datacenter, cabinet, hypervisor, "vm-name"));
            });
            System.out.println();
        }
        if (!atLeastOneSolution) {
            System.err.println("Failed to find a solution!");
        }

        model.getSolver().printStatistics();
    }

    private int[] hypervisorRange(String hypervisor, int[] cabinetRange) {
        final int[] candidates = new int[hypervisorPrefixes.size()];
        if (hypervisor == null) {
            return IntStream.of(0, hypervisorPrefixes.size()).toArray();
        }
        for (int value : cabinetRange) {
            AtomicInteger idx = new AtomicInteger();
            String dc = new ArrayList<>(cabinetPrefixes.keySet()).get(value);
            hypervisorPrefixes.forEach((k, v) -> {
                if (k.startsWith(dc)) {
                    candidates[idx.get()] = idx.get() + 1;
                }
                idx.incrementAndGet();
            });
        }
        return Arrays.stream(candidates).filter(c -> c != 0).map(c -> c - 1).toArray();
    }

    private int[] cabinetRange(String cabinet, int[] dcRange) {
        final int[] candidates = new int[cabinetPrefixes.size()];
        if (cabinet == null) {
            return IntStream.of(0, cabinetPrefixes.size()).toArray();
        }

        for (int value : dcRange) {
            AtomicInteger idx = new AtomicInteger();
            String dc = new ArrayList<>(dcPrefixes.keySet()).get(value);
            cabinetPrefixes.forEach((k, v) -> {
                if (k.startsWith(dc)) {
                    candidates[idx.get()] = idx.get() + 1;
                }
                idx.incrementAndGet();
            });
        }
        return Arrays.stream(candidates).filter(c -> c != 0).map(c -> c - 1).toArray();
    }

    private int[] dcRange(String region) {
        final AtomicInteger idx = new AtomicInteger();
        final int[] candidates = new int[dcPrefixes.size()];
        dcPrefixes.forEach((k, v) -> {
            if (k.startsWith(region)) {
                candidates[idx.get()] = idx.get() + 1;
            }
            idx.incrementAndGet();
        });
        return Arrays.stream(candidates).filter(c -> c != 0).map(c -> c - 1).toArray();
    }

    private static int regionInt(String region) {
        return Stream.of("Americas", "EMEA", "Asia")
                .sorted()
                .collect(toList()).indexOf(region);
    }

    private static Set<Node> createInventory(int count) {
//        Map<String, List<String>> dc = new HashMap<>();
//        dc.put("Americas", IntStream.range(1, new Random().nextInt(5)).mapToObj(i -> "dc-" + i).collect(toList()));
//        dc.put("EMEA", IntStream.range(1, new Random().nextInt(5)).mapToObj(i -> "dc-" + i).collect(toList()));
//        dc.put("Asia", IntStream.range(1, new Random().nextInt(5)).mapToObj(i -> "dc-" + i).collect(toList()));
//
//        Set<Node> results = new HashSet<>();
//        do {
//            List<String> regions = Arrays.asList(dc.keySet().toArray(new String[]{}));
//            String region = regions.get(new Random().nextInt(regions.size()));
//            List<String> dcs = dc.get(region);
//            String d = dcs.get(new Random().nextInt(dcs.size()));
//            int hypervisor = new Random().nextInt(5);
//            int vmId = new Random().nextInt(10);
//            results.add(new Node(region, d, new Random().nextInt(15), hypervisor, vmId));
//        } while(results.size() < count);
//        return results;

        return new HashSet<>(asList(
                new Node("Americas", "dc1", "1", "1", "1"),
                new Node("Americas", "dc1", "1", "1", "2"),
                new Node("Americas", "dc1", "1", "1", "3"),
                new Node("Americas", "dc1", "1", "1", "4"),
                new Node("Americas", "dc1", "1", "1", "5"),
                new Node("Americas", "dc1", "1", "2", "1"),
                new Node("Americas", "dc1", "1", "2", "1"),
//                new Node("Americas", "dc1", "1", "2", "2"),
//                new Node("Americas", "dc1", "1", "2", "3"),
//                new Node("Americas", "dc1", "1", "2", "4"),
//                new Node("Americas", "dc1", "1", "3", "5"),

                new Node("EMEA", "dc1", "1", "1", "1"),
//                new Node("EMEA", "dc1", "1", "1", "2"),
//                new Node("EMEA", "dc2", "1", "1", "3"),
//                new Node("EMEA", "dc2", "1", "1", "4"),
//                new Node("EMEA", "dc3", "1", "1", "5"),
//                new Node("EMEA", "dc3", "1", "2", "1"),
//                new Node("EMEA", "dc3", "1", "2", "2"),
//                new Node("EMEA", "dc4", "1", "2", "3"),
//                new Node("EMEA", "dc4", "1", "2", "4"),
//                new Node("EMEA", "dc4", "1", "3", "5"),

//                new Node("Asia", "dc1", "1", "1", "1"),
//                new Node("Asia", "dc1", "1", "1", "2"),
//                new Node("Asia", "dc1", "1", "1", "3"),
//                new Node("Asia", "dc1", "1", "1", "4"),
//                new Node("Asia", "dc1", "1", "1", "5"),
//                new Node("Asia", "dc1", "2", "2", "1"),
//                new Node("Asia", "dc1", "2", "2", "2"),
//                new Node("Asia", "dc1", "2", "2", "3"),
//                new Node("Asia", "dc1", "2", "2", "4"),
                new Node("Asia", "dc1", "2", "3", "5")
        ));
    }

    private static class Node {
        private final String os;
        private final String shape;
        private final String region;
        private final String dc;
        private final String cabinet;
        private final String hypervisor;
        private final String vmId;

        public Node(String region, String dc, String cabinet, String hypervisor, String vmId) {
            this("linux", "micro", region, dc, cabinet, hypervisor, vmId);
        }

        public Node(String os, String shape, String region, String dc, String cabinet, String hypervisor, String vmId) {
            this.region = region;
            this.dc = dc;
            this.cabinet = cabinet;
            this.hypervisor = hypervisor;
            this.vmId = vmId;
            this.os = os;
            this.shape = shape;
        }

        public String getRegion() {
            return region;
        }

        public String getDc() {
            return dc;
        }

        public String getCabinet() {
            return cabinet;
        }

        public String getHypervisor() {
            return hypervisor;
        }

        public String getVmId() {
            return vmId;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Node node = (Node) o;
            return region.equals(node.region) &&
                    dc.equals(node.dc) &&
                    cabinet.equals(node.cabinet) &&
                    hypervisor.equals(node.hypervisor) &&
                    vmId.equals(node.vmId);
        }

        @Override
        public int hashCode() {
            return Objects.hash(region, dc, cabinet, hypervisor, vmId);
        }

        @Override
        public String toString() {
            return "Node{" +
                    "os='" + os + '\'' +
                    ", shape='" + shape + '\'' +
                    ", region='" + region + '\'' +
                    ", dc='" + dc + '\'' +
                    ", cabinet='" + cabinet + '\'' +
                    ", hypervisor='" + hypervisor + '\'' +
                    ", vmId='" + vmId + '\'' +
                    '}';
        }
    }

    private static class NodeRequest {
        private final String os;
        private final String shape;
        private final String region;
        private final String dc;
        private final String cabinet;
        private final String hypervisor;

        NodeRequest(String region, String dc, String cabinet, String hypervisor) {
            this("linux", "micro", region, dc, cabinet, hypervisor);
        }

        NodeRequest(String os, String shape, String region, String dc, String cabinet, String hypervisor) {
            this.os = os;
            this.shape = shape;
            this.region = region;
            this.dc = dc;
            this.cabinet = cabinet;
            this.hypervisor = hypervisor;
        }

        public String getOs() {
            return os;
        }

        public String getShape() {
            return shape;
        }

        public String getRegion() {
            return region;
        }

        public String getDc() {
            return dc;
        }

        public String getCabinet() {
            return cabinet;
        }

        public String getHypervisor() {
            return hypervisor;
        }

        @Override
        public String toString() {
            return "NodeRequest{" +
                    "os='" + os + '\'' +
                    ", shape='" + shape + '\'' +
                    ", region='" + region + '\'' +
                    ", dc='" + dc + '\'' +
                    ", cabinet='" + cabinet + '\'' +
                    ", hypervisor='" + hypervisor + '\'' +
                    '}';
        }
    }
}
