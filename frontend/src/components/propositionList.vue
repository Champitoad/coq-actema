<style scoped>
ul {
    padding-top: 10px;
    padding-left: 10px;
    position: relative;
    border: 2px solid transparent;
    min-height: 100%;
    position: static;
}

ul.dragover {
    border: 2px solid #007bff;
}

li {
    line-height: 1.6em;
    font-size: 20px;
    font-family: "Computer Modern Sans", sans-serif;
    font-weight: bold;
    user-select: none;
    padding: 0px;
    border: none;
    position: static;
}

li>.overflow-container>.pi-predicate,
li>.overflow-container>.pi-expression {
    text-overflow: ellipsis;
    white-space: nowrap;
    overflow: hidden;
}

li span {
    padding: 0px 8px !important;
}

li .pi-predicate.in-hypothesis-zone {
    position: static;
    /*pointer-events: none;*/
}

li .pi-predicate.in-work-zone {
    position: absolute;
}

li .pi-expression.in-hypothesis-zone {
    position: static;
    /*pointer-events: none;*/
}

li .pi-expression.in-work-zone {
    position: absolute;
}

.btn-cut {
    border: none;
    max-width: 40%;
}

.btn-cut:focus {
    /* box-shadow: none !important; */
    outline: none !important;
}

.btn-clear {
    opacity: 0.2;
}

.btn-clear:hover {
    opacity: 1;
}

.btn-duplicate {
    opacity: 0.2;
}

.btn-duplicate:hover {
    opacity: 1;
}

.predicate-dropspace {
    height: 5px;
    width: 100%;
}

.predicate-dropspace.dragging {
    height: 6px;
}

.predicate-dropspace.droppable {
    height: 46px;
}

.plist .predicate-dropspace:last-child,
.plist .predicate-dropspace.droppable:last-child {
    height: 100px;
}

.overflow-container {
    overflow-x: hidden;
    width: auto;
    display: inline-block;
    height: auto;
}
</style>

<template>
    <ul class="list-group plist" :class="{ dragover: dragover }">
        <li class="list-group-item text-primary">
            <button class="btn btn-outline-success btn-cut d-inline-block w-50" @click="addNewExpression">
                <i class="fas fa-plus"></i> expr
            </button>
            <button class="btn btn-outline-primary btn-cut d-inline-block w-50" @click="addNewHypothesis">
                <i class="fas fa-plus"></i> hyp
            </button>
        </li>
        <template v-for="expression in getSortedExpressions()">
            <div class="predicate-dropspace" :key="'dropspace-' + expression.handle" :data-handle="expression.handle">
            </div>
            <li class="list-group-item text-success" :key="'li-' + expression.handle">
                <div class="overflow-container">
                    <expression :expression="expression" :selectMode="selectMode" :displayMode="displayMode"
                        :key="'expression-' + expression.handle" draggable="true" :ref="expression.handle">
                    </expression>
                </div>
                <button class="btn btn-sm btn-secondary-outline btn-transparent btn-clear d-inline-block float-right"
                    @click="onClear(expression)" title="Clear">
                    <i class="fas fa-archive"></i>
                </button>
            </li>
        </template>
        <template v-for="predicate in getSortedPredicates()">
            <div class="predicate-dropspace" :key="'dropspace-' + predicate.handle" :data-handle="predicate.handle">
            </div>
            <li class="list-group-item text-primary" :key="'li-' + predicate.handle">
                <div class="overflow-container">
                    <predicate :predicate="predicate" :selectMode="selectMode" :displayMode="displayMode"
                        :key="'predicate-' + predicate.handle" draggable="true" :ref="predicate.handle"></predicate>
                </div>
                <button class="btn btn-sm btn-secondary-outline btn-transparent btn-clear d-inline-block float-right"
                    @click="onClear(predicate)" title="Clear">
                    <i class="fas fa-archive"></i>
                </button>
                <button
                    class="btn btn-sm btn-secondary-outline btn-transparent btn-duplicate d-inline-block float-right"
                    @click="onDuplicate(predicate)" title="Duplicate">
                    <i class="fas fa-copy"></i>
                </button>
            </li>
        </template>
        <div class="predicate-dropspace last" data-handle="last"></div>
    </ul>
</template>

<script>
import _ from "lodash";
import PredicateVue from "./predicate.vue";
import ExpressionVue from "./expression.vue";

import Vue from 'vue';
import VueSweetalert2 from 'vue-sweetalert2';
import 'sweetalert2/dist/sweetalert2.min.css';

Vue.use(VueSweetalert2);

export default {
    props: ["goal", "context", "vars", "selectMode", "displayMode"],
    components: {
        predicate: PredicateVue,
        expression: ExpressionVue,
    },
    data: function () {
        return {
            dragover: false,
        };
    },
    methods: {
        getSortedPredicates: function () {
            var predicates = _.filter(this.context, o => {
                var meta = o.getmeta();
                var isInWorkZone = meta && meta.inWorkZone;
                return !isInWorkZone;
            });
            console.log("getSortedPredicates\n");
            console.log(predicates);
            return _.sortBy(predicates, ["position"]);
        },

        getSortedExpressions: function () {
            var expressions = _.filter(this.vars, o => {
                var meta = o.getmeta();
                var isInWorkZone = meta && meta.inWorkZone;
                return !isInWorkZone;
            });
            return _.sortBy(expressions, ["position"]);
        },

        addToWorkZone: function (predicate) {
            var meta = predicate.getmeta() || {};
            meta.inWorkZone = true;
            predicate.setmeta(meta);
            this.$parent.$forceUpdate();
            this.$forceUpdate();
        },

        setDragOver: function (b) {
            if (b) {
                $(this.$el).addClass("dragover");
            } else {
                $(this.$el).removeClass("dragover");
            }
        },

        addNewHypothesis: async function () {
            const { value: newHypothesisText } = await this.$swal.fire({
                title: "New Hypothesis",
                text: "Introduce a new hypothesis in the current goal.",
                input: "text",
                inputValue: "",
                showCancelButton: true,
                inputValidator: value => {
                    /* TODO */
                }
            });

            if (newHypothesisText) {
                this.$parent.sendCutHypothesis(this.goal, newHypothesisText);
            }
        },

        addNewExpression: async function () {
            const { value: newExpressionText } = await this.$swal.fire({
                title: "New Expression",
                text: "Introduce a new expression in the current goal.",
                input: "text",
                inputValue: "",
                showCancelButton: true,
                inputValidator: value => {
                    /* TODO */
                }
            });

            if (newExpressionText) {
                this.$parent.sendNewExpression(this.goal, newExpressionText);
            }
        },

        onDuplicate: function (predicate) {
            this.$parent.duplicateHyp(this.goal, predicate.handle);
        },

        onClear: function (predicate) {
            this.$parent.clearHyp(this.goal, predicate.handle);
        },
    }
};
</script>
