<style>
.pi-goal {
    position: absolute;
    margin-left: 25px;
}

.pi-goal .MathJax_Display {
    display: inline-block !important;
}

.pi-goal>.dropdown-toggle::after {
    position: relative;
    top: -5px;
    margin-left: 10px;
    display: none;
}

.pi-goal.dragged,
.pi-goal.dragged:hover,
.pi-goal.dragged:active {
    color: #ffffff !important;
    border-color: #dc3545 !important;
    background-color: #dc3545 !important;
}

.pi-goal:hover,
.pi-goal:active {
    color: #dc3545 !important;
    border-color: #dc3545 !important;
    background-color: #ffffff !important;
    cursor: pointer;
}

span.generalize {
    color: #2f8760;
    padding-left: 6px;
    padding-right: 6px;
    font-weight: bold;
    font-size: 24px;
    background-color: transparent;
    border: none;
    position: absolute;
    left: -36px;
    top: -2px;
    height: 36px;
}

span.generalize.highlight {
    background-color: #28a745;
    color: white;
}
</style>

<template>
    <div class="btn btn-outline-danger pi-btn pi-goal loading" :data-handle="subgoal.handle" v-html="html"
        @mousedown="mousedown" @mouseup="mouseup" @touchstart="touchstart" @touchend="touchend" v-touch:tap="tap"
        :id="uniqId()" :key="getTitle()"></div>
</template>

<script>
import _ from "lodash";
import ButtonVue from "./button.vue";

export default {
    extends: ButtonVue,
    props: ["subgoal", "selectMode", "displayMode"],
    created: function () {
        // goals are always in work zone
        this.assignMetadata({ inWorkZone: true });
    },
    computed: {
        alignment() {
            return "left";
        }
    },
    methods: {
        is: function (str) {
            return str == "subgoal"; // Bad, allow to break polymorphism
        },

        toHTML: function () {
            return "<span class='generalize'>⇒</span>" + this.subgoal.conclusion().html();
        },

        toString() {
            return this.subgoal.conclusion().tostring();
        },

        toMathML() {
            return this.subgoal.conclusion().mathml();
        },

        hasMultipleActions: function (e) {
            return this.subgoal.ivariants().length > 1;
        },

        getIvariants: function () {
            return this.subgoal.ivariants();
        },

        setMetadata: function (metadata) {
            this.subgoal.setmeta(metadata);
        },

        getMetadata: function () {
            return this.subgoal.getmeta();
        },

        getTitle: function () {
            var start = "Click to ";
            var variants = this.subgoal.ivariants();
            if (variants.length == 1) {
                return variants[0];
            }
            if (variants.length == 0) {
                return "No actions";
            }
            if (variants.length > 1) {
                return start + variants.join(" or\n");
            } else {
                return start + variants[0];
            }
        },

        getSubGoal: function () {
            return this.subgoal;
        },

        getHandle: function () {
            return this.subgoal.handle;
        },

        getRootId: function () {
            return this.getRootIdForType("C")
        },

        getPosition: function () {
            return 0; // There is only 1 goal per tab
        },

        getCurrentZone: function () {
            return "work-zone"; // only zone allowed for goals
        },

        quickSwitchToWorkZone: function () {
            // nothing to do
        }
    }
};
</script>
