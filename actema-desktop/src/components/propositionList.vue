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

.btn-archive {
    opacity: 0.2;
}

.btn-archive:hover {
    opacity: 1;
}

li.archived .pi-predicate,
li.archived .pi-expression {
    opacity: 0.1;
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
    width: calc(100% - 40px);
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
                :filter-by-query="false" :min-length="0" :preventHide="true">
                <div slot="suggestion-item" slot-scope="{ suggestion }">
                    <div>{{ suggestion.shortName }} : {{ suggestion.stmt }}</div>
                </div>
            </vue-simple-suggest>
        </li>
        <template v-for="expression in getSortedExpressions(false)">
            <div class="predicate-dropspace" :key="'dropspace-' + expression.handle" :data-handle="expression.handle">
            </div>
            <li class="list-group-item text-success" :class="{ archived: isArchived(expression) }"
                :key="'li-' + expression.handle">
                <div class="overflow-container">
                    <expression :expression="expression" :selectMode="selectMode" :displayMode="displayMode"
                        :key="'expression-' + expression.handle" draggable="true" :ref="expression.handle"></expression>
                </div>
                <button class="btn btn-sm btn-secondary-outline btn-transparent btn-archive d-inline-block float-right"
                    @click="toggleArchive(expression)">
                    <i class="fas fa-archive"></i>
                </button>
            </li>
        </template>
        <template v-for="predicate in getSortedPredicates(false)">
            <div class="predicate-dropspace" :key="'dropspace-' + predicate.handle" :data-handle="predicate.handle">
            </div>
            <li class="list-group-item text-primary" :class="{ archived: isArchived(predicate) }"
                :key="'li-' + predicate.handle">
                <div class="overflow-container">
                    <predicate :predicate="predicate" :selectMode="selectMode" :displayMode="displayMode"
                        :key="'predicate-' + predicate.handle" draggable="true" :ref="predicate.handle"></predicate>
                </div>
                <button class="btn btn-sm btn-secondary-outline btn-transparent btn-archive d-inline-block float-right"
                    @click="toggleArchive(predicate)">
                    <i class="fas fa-archive"></i>
                </button>
            </li>
        </template>
        <template v-for="expression in getSortedExpressions(true)">
            <div class="predicate-dropspace" :key="'dropspace-' + expression.handle" :data-handle="expression.handle">
            </div>
            <li class="list-group-item text-success" :class="{ archived: isArchived(expression) }"
                :key="'li-' + expression.handle">
                <div class="overflow-container">
                    <expression :expression="expression" :selectMode="selectMode" :displayMode="displayMode"
                        :key="'expression-' + expression.handle" draggable="true" :ref="expression.handle"></expression>
                </div>
                <button class="btn btn-sm btn-secondary-outline btn-transparent btn-archive d-inline-block float-right"
                    @click="toggleArchive(expression)">
                    <i class="fas fa-archive"></i>
                </button>
            </li>
        </template>
        <template v-for="predicate in getSortedPredicates(true)">
            <div class="predicate-dropspace" :key="'dropspace-' + predicate.handle" :data-handle="predicate.handle">
            </div>
            <li class="list-group-item text-primary" :class="{ archived: isArchived(predicate) }"
                :key="'li-' + predicate.handle">
                <div class="overflow-container">
                    <predicate :predicate="predicate" :selectMode="selectMode" :displayMode="displayMode"
                        :key="'predicate-' + predicate.handle" draggable="true" :ref="predicate.handle"></predicate>
                </div>
                <button class="btn btn-sm btn-secondary-outline btn-transparent btn-archive d-inline-block float-right"
                    @click="toggleArchive(predicate)">
                    <i class="fas fa-archive"></i>
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
            lemmaSearchText: ""
        };
    },
    methods: {
        getSortedPredicates: function (archived) {
            var predicates = _.filter(this.context, o => {
                var meta = o.getmeta();
                var isInWorkZone = meta && meta.inWorkZone;
                var isArchived = (meta && meta.archived) || false;
                var hasRequiredArchiveStatus = !(archived ^ isArchived);
                return !isInWorkZone && hasRequiredArchiveStatus;
            });
            return _.sortBy(predicates, ["position"]);
        },

        getSortedExpressions: function (archived) {
            var expressions = _.filter(this.vars, o => {
                var meta = o.getmeta();
                var isInWorkZone = meta && meta.inWorkZone;
                var isArchived = (meta && meta.archived) || false;
                var hasRequiredArchiveStatus = !(archived ^ isArchived);
                return !isInWorkZone && hasRequiredArchiveStatus;
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

        addLemma: async function (lemma) {
            //this.$parent.applyAddLemma(this.goal, lemma.name);
            console.log("Clicked on lemma: " + lemma.name);
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

        toggleArchive: function (predicate) {
            var archived = this.isArchived(predicate);
            var metadata = predicate.getmeta() || {};
            Object.assign(metadata, { archived: !archived });
            predicate.setmeta(metadata);
            this.$parent.$forceUpdate();
        },

        isArchived: function (predicate) {
            var metadata = predicate.getmeta() || {};
            return metadata.archived || false;
        },

        updateLemmaList: function () {
            console.log("Updating lemma dropdown.");
            let selection = this.$parent.getSelection(this.goal);
            let lemmas = Object.entries(this.$parent.proofState.getlemmas(selection));
            console.log("Lemma count: " + lemmas.length);

            // Get the short version of a lemma name.
            // Example : "Coq.ZArith.BinInt.Z.Private_Div.NZQuot.add_mod"
            // gets shortened to "add_mod".
            let shorten = function (name) {
                let parts = name.split('.');
                return parts[parts.length - 1];
            };

            this.lemmaList = _.map(lemmas, l => {
                return { shortName: shorten(l[0]), name: l[0], stmt: l[1] }
            });
        }
    }
};
</script>
