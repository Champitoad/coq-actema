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

.search-lemma-bar {
    margin: 10px 10px 20px 0;
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
    opacity: 0.2;
}

.predicate-dropspace {
    height: 5px;
    /* background-color: red; */
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
    width: calc(100% - 80px);
    display: inline-block;
    height: 44px;
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
        <li class="list-group-item">
            <vue-simple-suggest class="search-lemma-bar" placeholder="Search lemma..." v-model="lemmaSearchText"
                display-attribute="shortName" value-attribute="name" @select="addLemma" :list="lemmaList"
                :filter-by-query="false" :min-length="0" :preventHide="true" :key="lemmaKey" ref="lemmaSearchBar">
                <div slot="suggestion-item" slot-scope="{ suggestion }">
                    <div>{{ suggestion.shortName }} : {{ suggestion.stmt }}</div>
                </div>
            </vue-simple-suggest>
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

import VueSimpleSuggest from 'vue-simple-suggest'
import 'vue-simple-suggest/dist/styles.css' // Optional CSS

Vue.use(VueSweetalert2);

export default {
    props: ["goal", "context", "vars", "selectMode", "displayMode"],
    components: {
        predicate: PredicateVue,
        expression: ExpressionVue,
        VueSimpleSuggest
    },
    data: function () {
        return {
            lemmaList: [],
            dragover: false,
            lemmaSearchText: "",
            // A variable used to force a re-render of the lemma list when needed.
            // This is known as the key-changing technique. For more information see :
            // https://michaelnthiessen.com/force-re-render
            lemmaKey: 0,
        };
    },
    methods: {
        getSortedPredicates: function () {
            var predicates = _.filter(this.context, o => {
                var meta = o.getmeta();
                var isInWorkZone = meta && meta.inWorkZone;
                return !isInWorkZone;
            });
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

        // Callback invoked when we click on an entry in the lemma dropdown (list).
        addLemma: async function (lemma) {
            this.$parent.sendLemma(this.goal, lemma.name);
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

        updateLemmaList: function () {
            let lemmas = Object.entries(this.$parent.proofState.getlemmas());

            this.lemmaList = _.map(lemmas, l => {
                //console.log(l);
                return { name: l[1][0], shortName: l[1][1], stmt: l[1][2] }
            });

            // Force a re-render of the lemma list.
            this.lemmaKey += 1;
        },

        getLemmaSearchText: function () {
            return this.lemmaSearchText;
        },

        focusLemmaSearchBar: function () {
            // For some reason using "setTimeout" is necessary here.
            // For somewhat of an explanation read :
            // https://bobbyhadz.com/blog/focus-not-working-in-javascript
            setTimeout(() => {
                this.$refs.lemmaSearchBar.input.focus();
            }, 0);
        }
    }
};
</script>
